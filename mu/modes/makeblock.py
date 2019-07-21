"""
A mode for working with Makeblock's HaloCode, Codey Rocky and MakeX devices.

Copyright (c) 2015-2017 Nicholas H.Tollervey and others (see the AUTHORS file).

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
"""

import os
import ctypes
import time
import threading
import sys
import os.path
import logging
import semver
import getopt
import re
import random
import codecs, binascii
from subprocess import check_output
from tokenize import TokenError
from mu.logic import HOME_DIRECTORY
from mu.contrib import uflash, microfs, esptool
from mu.modes.api import MAKEBLOCK_APIS, SHARED_APIS
from mu.modes.base import MicroPythonMode
from mu.interface.panes import CHARTS
from PyQt5.QtCore import QObject, QThread, pyqtSignal, QTimer, pyqtSlot
from PyQt5.QtWidgets import QApplication, QWidget, QComboBox, QFontComboBox, QLineEdit, QMessageBox, QVBoxLayout, QLabel, QHBoxLayout, QGridLayout, QPushButton, QFileDialog, QDialog
from mu.interface import Window

# use serial 
USE_PYSERIAL_FALG = False

if USE_PYSERIAL_FALG:
    import serial
    import serial.tools.list_ports

# We can run without nudatus
can_minify = True
try:
    import nudatus
except ImportError:  # pragma: no cover
    can_minify = False

logger = logging.getLogger(__name__)

class makeblock_config():
    def __init__(self):
        self.COMMAND_MAX_TIME_OUT     = 10
        self.FILE_BLOCK_SIZE          = 240
        self.frame_header_str         = "F3"
        self.frame_end_str            = "F4"
        self.protocol_id_str          = "01"
        self.dev_id_str               = "00"
        self.srv_id_str               = "5E"
        self.file_header_cmd_id_str   = "01"
        self.file_block_cmd_id_str    = "02"
        self.file_delete_str          = "03"
        self.file_state_cmd_id_str    = "F0"
        self.file_type_str            = "00"

class FileTransferFSM(makeblock_config):
    def __init__(self):
        super().__init__()
        self.FRAME_HEAD               = int(self.frame_header_str, 16) 
        self.FRAME_END                = int(self.frame_end_str, 16)
        self.DEV_ID                   = int(self.dev_id_str, 16)
        self.SRV_ID                   = int(self.srv_id_str, 16)
        self.CMD_STATE_ID             = int(self.file_state_cmd_id_str, 16)
        self.FTP_FSM_HEAD_S           = 0
        self.FTP_FSM_HEAD_CHECK_S     = 1
        self.FTP_FSM_LEN1_S           = 2
        self.FTP_FSM_LEN2_S           = 3
        self.FTP_FSM_DATA_S           = 4
        self.FTP_FSM_CHECK_S          = 5
        self.FTP_FSM_END_S            = 6

        self.__state = self.FTP_FSM_HEAD_S
        self.__buf = []
        self.__data_len = 0
        self.__checksum = 0x00
        self.__headchecksum = 0x00
        self.__recv_head_checksum = 0x00
        
        self.frame_received_process = None

    def get_state(self):
        return self.__state

    def set_state(self, s):
        self.__state = s

    def push_chars(self, data):
        for c in data:
            ret = self.push_char(c)
            if ret:
                if self.frame_received_process:
                    self.frame_received_process(ret)
                self.clear_buf()

    def push_char(self, c):
        if self.FTP_FSM_HEAD_S == self.__state:
            if self.FRAME_HEAD == c:
                self.__state = self.FTP_FSM_HEAD_CHECK_S
                self.__buf.clear()
                self.__checksum = 0
                self.__headchecksum = c

        elif self.FTP_FSM_HEAD_CHECK_S == self.__state:
            self.__recv_head_checksum = c
            self.__state = self.FTP_FSM_LEN1_S

        elif self.FTP_FSM_LEN1_S == self.__state:
            self.__headchecksum += c
            self.__data_len = c
            self.__state = self.FTP_FSM_LEN2_S

        elif self.FTP_FSM_LEN2_S == self.__state:
            self.__headchecksum += c
            if self.__headchecksum == self.__recv_head_checksum:
                self.__data_len += c * 256
                self.__state = self.FTP_FSM_DATA_S
            else:
                self.__state = self.FTP_FSM_HEAD_S

        elif self.FTP_FSM_DATA_S == self.__state:
            self.__checksum += c
            self.__buf.append(c)
            if len(self.__buf) == self.__data_len:
                self.__state = self.FTP_FSM_CHECK_S

        elif self.FTP_FSM_CHECK_S == self.__state:
            if (self.__checksum & 0xFF) == c:
                self.__state = self.FTP_FSM_END_S
            else:
                self.__state = self.FTP_FSM_HEAD_S
                
        elif self.FTP_FSM_END_S == self.__state:
            if self.FRAME_END == c:
                self.__state = self.FTP_FSM_HEAD_S
                return self.__buf
            else:
                self.__state = self.FTP_FSM_HEAD_S 

    def clear_buf(self):
        self.__buf.clear()

    def get_buf(self):
        return self.__buf

class file_content_parse(makeblock_config):
    def __init__(self, content = ""):
        super().__init__()
        self.update(content)

    def update(self, content):
        self.content = content
        self.content_len = len(content)
        self.write_offset = 0

    def __bytes_to_hex_str(self, bytes_data):
        return " ".join("{:02x}".format(c) for c in bytes_data)

    def __calc_add_checksum(self, data):
        ret = 0
        for c in data:
            ret = ret + c
        return ret & 0xFF

    def __calc_32bit_xor(self, data):
        bytes_len = len(data)
        data_bytes = bytes(data)
        checksum = bytearray.fromhex("00 00 00 00")
        for i in range(int(bytes_len / 4)):
            checksum[0] = checksum[0] ^ data_bytes[i * 4 + 0]
            checksum[1] = checksum[1] ^ data_bytes[i * 4 + 1]
            checksum[2] = checksum[2] ^ data_bytes[i * 4 + 2]
            checksum[3] = checksum[3] ^ data_bytes[i * 4 + 3]

        if (bytes_len % 4):
            for i in range(bytes_len % 4):
                checksum[0 + i] = checksum[0 + i] ^ data_bytes[4 * int(bytes_len / 4) + i]
        return checksum

    def create_head_frame(self, target_file_path):
        # file header
        # 1(file_type) + 4(file_size) + 4(file_check_sum) = 0x09
        cmd_len_str = self.__bytes_to_hex_str((0x09 + len(target_file_path)).to_bytes(2, byteorder = 'little'))
        input_file_size_str = self.__bytes_to_hex_str(self.content_len.to_bytes(4, byteorder = 'little'))
        input_file_checksum_str = self.__bytes_to_hex_str(self.__calc_32bit_xor(self.content))
        input_file_name_str = self.__bytes_to_hex_str(bytes(target_file_path, encoding = 'utf-8'))
        frame_data_str = self.protocol_id_str + " " + self.dev_id_str + " " + self.srv_id_str + " " + \
                         self.file_header_cmd_id_str + " " + cmd_len_str + " " + self.file_type_str + " " + \
                         input_file_size_str + " " + input_file_checksum_str + " " + input_file_name_str
        frame_data_len = len(bytes.fromhex(frame_data_str))
        frame_data_len_str = self.__bytes_to_hex_str((frame_data_len).to_bytes(2, byteorder='little'))
        frame_head_checkusum_str = self.__bytes_to_hex_str(self.__calc_add_checksum(bytes.fromhex(self.frame_header_str + frame_data_len_str)).to_bytes(1, byteorder = 'little'))
        frame_checksum_str = self.__bytes_to_hex_str(self.__calc_add_checksum(bytes.fromhex(frame_data_str)).to_bytes(1, byteorder = 'little'))
        
        send_head_str = self.frame_header_str + " " + frame_head_checkusum_str + " " + frame_data_len_str + " " + \
                        frame_data_str + " " + frame_checksum_str + " " + self.frame_end_str

        return bytes.fromhex(send_head_str)
    
    def get_next_block(self):
        if self.write_offset >= self.content_len:
            print("no data to write")
            return 

        if (self.write_offset + self.FILE_BLOCK_SIZE) < self.content_len:
            send_file_size = self.FILE_BLOCK_SIZE
        else:
            send_file_size = self.content_len - self.write_offset

        file_offset_str = self.__bytes_to_hex_str(self.write_offset.to_bytes(4, byteorder = 'little'))
        cmd_len_str = self.__bytes_to_hex_str((0x04 + send_file_size).to_bytes(2, byteorder = 'little'))
        file_block_str = self.__bytes_to_hex_str(bytes(self.content[self.write_offset: self.write_offset + send_file_size]))
        frame_data_str = self.protocol_id_str + " " + self.dev_id_str + " " + self.srv_id_str + " " + self.file_block_cmd_id_str + \
                         " " + cmd_len_str + " " + file_offset_str + " " + file_block_str
        frame_data_len = len(bytes.fromhex(frame_data_str))
        frame_data_len_str = self.__bytes_to_hex_str((frame_data_len).to_bytes(2, byteorder = 'little'))
        frame_head_checkusum_str = self.__bytes_to_hex_str(self.__calc_add_checksum(bytes.fromhex(self.frame_header_str + frame_data_len_str)).to_bytes(1, byteorder = 'little'))
        frame_checksum_str = self.__bytes_to_hex_str(self.__calc_add_checksum(bytes.fromhex(frame_data_str)).to_bytes(1, byteorder = 'little'))

        send_block_str = self.frame_header_str + " " + frame_head_checkusum_str + " " + frame_data_len_str + \
                         " " + frame_data_str + " " + frame_checksum_str + " " + self.frame_end_str

        send_block_bytes = bytearray.fromhex(send_block_str)

        self.write_offset += send_file_size
        
        return send_block_bytes
    
    def get_current_percentage(self):
        return int(100 * self.write_offset / self.content_len)

class makeblock_communication():
    def __init__(self):
        self.serial_fd = None
        self.input_file_content = None
        self.target_file_path = None

        self.ftp_process = FileTransferFSM()
        self.ftp_process.frame_received_process = self.__frame_process
        self.flash_start_signal = pyqtSignal()
        self.flash_continue_signal = pyqtSignal()
        self.file_content = file_content_parse()

        self.show_status_message = None

        self.process_status = 0
        self.ser_close = None

    def update_paras(self, serial, content, target_file_path):
        self.serial_fd = serial
        self.input_file_content = content
        self.target_file_path = target_file_path
        self.file_content.update(content)
        self.process_status = 0
        
    def send_file_content(self, ser = None, input_file_data = None, target_file_path = None):
        print("send_file_content run")

        if ser == None:
            ser = self.serial_fd
        if input_file_data == None:
            input_file_data = self.input_file_content
        if target_file_path == None:
            target_file_path = self.target_file_path
        
        if self.process_status == 0:
            frame = self.file_content.create_head_frame(self.target_file_path)
            if frame:
               ser.write(frame)
               self.process_status = 1
        else:
            frame = self.file_content.get_next_block()
            
            if frame:
                ser.write(frame)
                self.show_status_message("transmitting: %s%s" %('%', self.file_content.get_current_percentage(), ))
        
        print("send_file_content done")

    def __frame_process(self, frame):
        if (0x01 == frame[0] and 0x00 == frame[6]):
            if self.file_content.get_current_percentage() < 100:
                self.send_file_content()
            else:
                self.show_status_message(_("Complete file transfer!"))
                self.process_status = 0
        else:
            pass


class MakeblockMode(MicroPythonMode):
    """
    Represents the functionality required by the Makeblock mode.
    """

    name = _('Makeblock MicroPython')
    description = _(
        "Use MicroPython on Makeblock's HaloCode, Codey Rocky and more.")
    icon = 'makeblock'

    valid_boards = [
        (6790, 29987),  # Makeblock Device Vid/Pid
    ]

    python_script = ''
    
    def __init__(self, editor, view):
        self.communication = makeblock_communication()
        super().__init__(editor, view)
        self.view = view

    def actions(self):
        """
        Return an ordered list of actions provided by this module. An action
        is a name (also used to identify the icon) , description, and handler.
        """
        buttons = [
            {
                'name': 'run',
                'display_name': _('Upload'),
                'description': _('Upload your code onto the Makeblock devices.'),
                'handler': self.flash,
                'shortcut': 'F2',
            }, 
            {
                'name': 'repl',#png image name
                'display_name': _('REPL'), 
                'description': _('Use the REPL for live coding.'),
                'handler': self.toggle_repl,
                'shortcut': 'F1',
            },
            {
                'name': 'flash_py',
                'display_name': _('Firmware'),
                'description': _('Update firmware.'),
                'handler': self.firmware_update,
                'shortcut': 'F3',
            },]
        
        if CHARTS:
            buttons.append({
                'name': 'plotter',
                'display_name': _('Plotter'),
                'description': _('Plot incoming REPL data.'),
                'handler': self.toggle_plotter,
                'shortcut': 'CTRL+Shift+P',
            })
        
        return buttons

    def api(self):
        """
        Return a list of API specifications to be used by auto-suggest and call
        tips.
        """
        return SHARED_APIS + MAKEBLOCK_APIS

    def find_port(self, vid=6790, pid=29987):
        """
        Find the port of Makeblock's devices
        Return: Makeblock Device or None if not found
        """
        if USE_PYSERIAL_FALG:
            for port in serial.tools.list_ports.comports():
                if port.vid == vid and port.pid == pid:
                    return port.device
            return None
        else:
            return self.find_device()[0]

# script update process
    def close_serial(self):
        repl_on = self.repl
        plotter_on = self.plotter
        
        if (not repl_on) and (not plotter_on):
            self.view.close_serial_link()

    def flash(self):
        """
        Upload Code to Makeblock Devices
        """
        port = self.find_port()

        if port == None:
            m = _('Could not find an attached Makeblock Device')
            info = _("Please attach your Makeblock device (Codey Rocky or HaloCode)"
                        " with USB Cable")
            self.view.show_message(m, info)
        else:
            self.communication.show_status_message = self.editor.show_status_message
            tab = self.view.current_tab
            if tab is None:
                # There is no active text editor. Exit.
                return
            python_script = tab.text().encode('utf-8')
            
            if USE_PYSERIAL_FALG:
                pass
            else:
                if not self.view.serial:
                    try:
                        self.view.open_serial_link(port)
                    except IOError as ex:
                        self.view.close_serial_link()
                        logger.error(ex)
                        info = _("CAN not open port {}, please check whether this port has been connected.").format(port)
                        self.view.show_message(str(ex), info)
                        return
                    except Exception as ex:
                        self.view.close_serial_link()
                        logger.error(ex)
                        return
            
            self.communication.ser_close = self.close_serial
            self.view.data_received.connect(self.communication.ftp_process.push_chars)
            self.communication.update_paras(self.view.serial, python_script, '/flash/main.py')
            self.communication.send_file_content()

# firmware update process
    def _firmware_update_process(self, info, per):
        self.editor.show_status_message(info + ": %s%s" %('%', per, ))
    
    def firmware_update(self):
        repl_on = self.repl
        plotter_on = self.plotter
        
        if repl_on:
            self.remove_repl()

        if plotter_on:
            self.remove_plotter()

        port = self.find_port()
        if not self.view.serial:
            try:
                self.view.open_serial_link(port)
            except IOError as ex:
                self.view.close_serial_link()
                logger.error(ex)
                info = _("CAN not open port {}, please check whether this port has been connected.").format(port)
                self.view.show_message(str(ex), info)
                return
            except Exception as ex:
                self.view.close_serial_link()
                logger.error(ex)
                return

        try:
            self.view.close_serial_link()
        except:
            pass
        
        qd = QDialog()
        fname = QFileDialog.getOpenFileName(qd, 'open file', '', 'Firmware (*.bin)') 
        if fname[0] == "":
            return
        
        if fname[0][-4 : ] != ".bin":
            return
                
        firmware_update_thread = threading.Thread(target = self.firmware_update_task, args = (port, fname[0]))
        firmware_update_thread.start()

    def firmware_update_task(self, port, firmware_name):
        old_argv = sys.argv        
        sys.argv = ['', '--port', port, 'write_flash', '--flash_mode', 'dio', '--flash_size', '4MB', '0x1000', firmware_name]

        try:
            esptool.set_extern_show_function(self._firmware_update_process, _("update firmware:"))
            # self.editor.show_status_message(_("firmwrae update preparing..."))
            esptool._main()
            self.editor.show_status_message(_("firmwrae update completed!"))

        except Exception as e:
            self.editor.show_status_message(_("firmwrae update failed!"))

        sys.argv = old_argv


