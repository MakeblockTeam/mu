"""
Contains definitions for the MicroPython Makeblock's HaloCode and Codey Rocky related APIs so they can be
used in the editor for autocomplete and call tips.

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


MAKEBLOCK_APIS = [
    # RNG
    _("random.getrandbits(n) \nReturn an integer with n random bits."),
    _("random.seed(n) \nInitialise the random number generator with a known integer 'n'."),
    _("random.randint(a, b) \nReturn a random whole number between a and b (inclusive)."),
    _("random.randrange(stop) \nReturn a random whole number between 0 and up to (but not including) stop."),
    _("random.choice(seq) \nReturn a randomly selected element from a sequence of objects (such as a list)."),
    _("random.random() \nReturn a random floating point number between 0.0 and 1.0."),
    _("random.uniform(a, b) \nReturn a random floating point number between a and b (inclusive)."),
    # OS
    _("os.listdir() \nReturn a list of the names of all the files contained within the local\non-device file system."),
    _("os.remove(filename) \nRemove (delete) the file named filename."),
    _("os.size(filename) \nReturn the size, in bytes, of the file named filename."),
    _("os.uname() \nReturn information about MicroPython and the device."),
    # SYS
    _("sys.version"),
    _("sys.version_info"),
    _("sys.implementation"),
    _("sys.platform"),
    _("sys.byteorder"),
    _("sys.print_exception(ex) \nPrint to the REPL information about the exception 'ex'."),
    # time
    _("time.sleep()"),

    # mbuild
    ## dc motor
    _("mbuild.dc_motor_driver.set_power(speed, index = 1) \nSet the speed of the DC Motor.\n\nspeed: a 1-100 number, the motor speed"),
    _("mbuild.dc_motor_driver.change_power(speed, index = 1) \nIncrease the speed of the DC Motor\n\n"
        "speed: -100~100 number, the increase of the motor speed"),
    _("mbuild.dc_motor_driver.get_power(index = 1) \nGet the current power level of the DC Motor"),
    _("mbuild.dc_motor_driver.get_load(index = 1) \nget the electricity current value inside the motor.\n"
        "the heavier the current (e.g. when the motor is stuck), the higher the value"),
    _("mbuild.dc_motor_driver.stop_all() \nStop the DC Motor"),
    
    ## dual rgb
    _("mbuild.dual_rgb_sensor.study(index = 1) \n"),
    _("mbuild.dual_rgb_sensor.get_all_data(index = 1) \n"),
    _("mbuild.dual_rgb_sensor.get_intensity(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.is_state(state, index = 1) \n"),
    _("mbuild.dual_rgb_sensor.get_offset_track_value(index = 1) \n"),
    _("mbuild.dual_rgb_sensor.is_color(channel, color, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.set_led_color(color, index = 1) \n"),
    _("mbuild.dual_rgb_sensor.is_on_track(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.is_on_background(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.set_motor_diff_speed_kp(value) \n"),
    _("mbuild.dual_rgb_sensor.get_motor_diff_speed(index = 1) \n"),
    _("mbuild.dual_rgb_sensor.get_red(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.get_green(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.get_blue(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.get_reflected_light(channel, index = 1) \nchannel:'RGB1'/'RGB2'"),
    _("mbuild.dual_rgb_sensor.set_light_color(color, index = 1) \n"),
    _("mbuild.dual_rgb_sensor.set_all_data_report_mode(mode, timestamp, index = 1) \n"),

    ## humiture
    _("mbuild.humiture_sensor.get_relative_humidity(index = 1) \nget the relative humidity in percentage.\n\n"
        "returns a value of 1-100"),
    _("mbuild.humiture_sensor.get_temperature(opt = 'celsius', index = 1) \nget the temperature of the humiture sensor\n\n"
        "opt:the temperature system of the return value, 'celsius' or 'fahrenheit'"),

    ## led panel
    _("mbuild.led_panel.show_image(image, pos_x = 0, pos_y = 0, time_s = None, index = 1) \n"),
    _("mbuild.led_panel.show(var, pos_x = None, pos_y = None, wait = True, index = 1) \n"),
    _("mbuild.led_panel.set_pixel(pos_x, pos_y, status, index = 1) \n"),
    _("mbuild.led_panel.get_pixel(pos_x, pos_y, index = 1) \n"),
    _("mbuild.led_panel.toggle_pixel(pos_x, pos_y, index = 1) \n"),
    _("mbuild.led_panel.clear(index = 1) \n"),
    
    ## led_strip
    _("mbuild.led_strip.set_single(led_index, red_value, green_value, blue_value, index = 1) \n"),
    _("mbuild.led_strip.set_all(red_value, green_value, blue_value, index = 1) \n"),
    _("mbuild.led_strip.off_all(index = 1) \n"),
    _("mbuild.led_strip.set_red(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.set_green(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.set_blue(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.change_red(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.change_green(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.change_blue(led_index, value, index = 1) \n"),
    _("mbuild.led_strip.set_mode(mode, index =1) \n"),
    _("mbuild.led_strip.set_block(led_num, data, index = 1) \n"),
    _("mbuild.led_strip.set_effect(mode, speed, data, index = 1) \n"),

    ## pir
    _("mbuild.pir_sensor.is_activated(index = 1) \n"),
    _("mbuild.pir_sensor.get_count(index = 1) \n"),
    _("mbuild.pir_sensor.reset_count(index = 1) \n"),
    
    ## ranging sensor
    _("mbuild.ranging_sensor.get_distance(index = 1) \n"),
    
    ## servo
    _("mbuild.servo_driver.set_angle(position, index = 1) \n"),
    _("mbuild.servo_driver.change_angle(position, index = 1) \n"),
    _("mbuild.servo_driver.get_angle(index = 1) \n"),
    _("mbuild.servo_driver.get_load(index = 1) \n"),

    ## slider
    _("mbuild.slider.get_value(index = 1) \n"),

    ## speaker
    _("mbuild.speaker.stop_sounds(index = 1) \n"),
    _("mbuild.speaker.set_volume(value, index = 1) \n"),
    _("mbuild.speaker.change_volume(value, index = 1) \n"),
    _("mbuild.speaker.get_volume(index = 1) \n"),
    _("mbuild.speaker.play_note(note, beat = None, index = 1) \n"),
    _("mbuild.speaker.play_tone(frequency, time_s = None, index = 1) \n"), 
    _("mbuild.speaker.play_melody(sound_name, index = 1) \n"),
    _("mbuild.speaker.play_melody_until_done(sound_name, index = 1) \n"),
    _("mbuild.speaker.is_playing(index = 1) \n"),

    ## ultrasonic
    _("mbuild.ultrasonic_sensor.get_distance(index = 1) \n"),

    ## angle sensor
    _("mbuild.angle_sensor.get_angle(index = 1) \n"),
    _("mbuild.angle_sensor.get_angle_speed(index = 1) \n"),
    _("mbuild.angle_sensor.is_rotating_clockwise(index = 1) \n"),
    _("mbuild.angle_sensor.is_rotating_anticlockwise(index = 1) \n"),
    _("mbuild.angle_sensor.reset_angle(index = 1) \n"),

    ## button
    _("mbuild.button.is_pressed(index = 1) \n"),
    _("mbuild.button.get_count(index = 1) \n"),
    _("mbuild.button.reset_count(index = 1): \n"),

    ## flame sensor
    _("mbuild.flame_sensor.is_active(index = 1) \n"),
    _("mbuild.flame_sensor.get_value(index = 1) \n"),

    ## mq2 gas sensor
    _("mbuild.mq2_gas_sensor.is_active(threshold_level = 'middle', index = 1) \nlevel:'middle'/'high'/'low'"),
    _("mbuild.mq2_gas_sensor.get_value(index = 1) \n"),

    ## ir transceiver
    _("mbuild.ir_transceiver.receive(index = 1) \n"),
    _("mbuild.ir_transceiver.send(message, index = 1) \n"),
    _("mbuild.ir_transceiver.send_learned_result(id = 0, index = 1) \nid:0/1"),
    _("mbuild.ir_transceiver.learn(time_ms = 2000, id = 0, index = 1) \n"),
    _("mbuild.ir_transceiver.receive_remote_code(index = 1) \nreturn a list:[address, value]"),

    ## joystick
    _("mbuild.joystick.get_value(opt, index = 1) \nopt:'x'/'y'/'all'"),
    _("mbuild.joystick.is_active(opt, index = 1) \nopt:'x'/'y'/'all'"),

    ## light sensor
    _("mbuild.light_sensor.get_value(index = 1) \n"),

    ## motion sensor
    _("mbuild.motion_sensor.get_acceleration(axis, index = 1) \naxis:'x'/'y'/'z'"),
    _("mbuild.motion_sensor.get_gyroscope(axis, index = 1) \n'x'/'y'/'z'"),
    _("mbuild.motion_sensor.get_rotation(axis, index = 1) \n'x'/'y'/'z'"),
    _("mbuild.motion_sensor.reset_rotation(axis = 'all', index = 1) \n'x'/'y'/'z'/'all'"),
    _("mbuild.motion_sensor.is_shaked(level = 'usual', index = 1) \nlevel:'light'/'usual'/'strong'"),
    _("mbuild.motion_sensor.get_shake_strength(index = 1) \n"),
    _("mbuild.motion_sensor.get_pitch(index = 1) \n"),
    _("mbuild.motion_sensor.get_roll(index = 1) \n"),
    _("mbuild.motion_sensor.is_tilted_left(index = 1) \n"),
    _("mbuild.motion_sensor.is_tilted_right(index = 1) \n"),
    _("mbuild.motion_sensor.is_tilted_forward(index = 1) \n"),
    _("mbuild.motion_sensor.is_tilted_backward(index = 1) \n"),
    _("mbuild.motion_sensor.is_face_up(index = 1) \n"),
    _("mbuild.motion_sensor.is_face_down(index = 1) \n"),
    _("mbuild.motion_sensor.is_upright(index = 1) \n"),

    ## mult touch
    _("mbuild.multi_touch.is_active(position, index = 1) \nposition:1~8"),
    _("mbuild.multi_touch.get_value(position, index = 1) \nposition:1~8"),
    _("mbuild.multi_touch.reset_threshold(index = 1) \n"),
    _("mbuild.multi_touch.set_sensitivity(sen, index = 1) \n"),

    ## soil moisture
    _("mbuild.soil_moisture.get_humidity(index = 1) \n"),

    ## sound sensoor
    _("mbuild.sound_sensor.get_loudness(index = 1) \n"),

    ## temp sensor
    _("mbuild.temp_sensor.get_temperature(opt = 'celsius', index = 1) \nopt:'celsius'/'fahrenheit'"),

    # System state objects.
    _("halo.get_timer() \n"),
    _("halo.reset_timer() \n"),
    # button
    _("halo.button.is_pressed() \nreturn True if the center button of Halocode is pressed"),
    # cloud_message
    _("halo.cloud_message.start(topic_head)\n"),
    _("halo.cloud_message.get_info(msg) \n"),
    _("halo.cloud_message.broadcast(message, value = "") \n"),
    # led
    _("halo.led.show_single(led_id, r, g, b, percentage = 100) \nChange the color of a single LED light in the light ring\n\n"
        "led_id: a 1-12 number, the index of the LED light\nr, g, b: the 0-255 RGB value of the color\n"
        "percentage: a 1-100 number, the strength of the light"),
    _("halo.led.show_all(r, g = 0, b = 0, percentage = 100) \nChange the color of all the LED lights in the light ring\n\n"
        "r, g, b: the 0-255 RGB value of the color\n"
        "percentage: a 1-100 number, the strength of the light"),
    _("halo.led.off_single(led_id) \nTurn off a single light in the LED light ring.\n\n"
        "led_id: a 1-12 number, the index of the LED light\n"),
    _("halo.led.off_all() \nTurn off all the lights in the LED light ring"),
    _("halo.led.clear() \n"),
    _("halo.led.show_ring(color_str, offset = 0) \n"),
    _("halo.led.ring_graph(percentage) \n"),
    _("halo.led.show_animation(name_string) \nspoondrift/meteor/rainbow/firefly/flash_red/flash_orange/right"),
    _("halo.led.show_full_color(data, offset = 0) \n"),
    # mesh
    _("halo.mesh.start_group(group_name) \n"),
    _("halo.mesh.join_group(group_name) \n"),
    _("halo.mesh.get_info(msg) \n"),
    _("halo.mesh.broadcast(message, value = "") \n"),
    # microphone
    _("halo.microphone.get_loudness(type = 'average') \naverage/maximum"),
    # pin
    _("halo.pin0.write_digital(value) \nOutput digital value to pin\n\nvalue: 0 or 1 number for the output"),
    _("halo.pin0.servo_write(value) \nSet the angle or the servo PWM high pulse length\n\n"
        "value: a number, servo angle for 0-180; high pulse length(us) for 544-20000\n"
        "number between 180 and 544 will be treated as 180"),
    _("halo.pin0.read_analog() \nRead and return the analog value of the pin.\n\n"
        "Returns number 0-3300, the voltage(mv) of the signal"),
    _("halo.pin0.write_analog(value) \Output a PWM signal through the pin.\n\nvalue: a 0-1023 number "),
    _("halo.pin0.is_touched() \nReturns true if the pin 0 is touched by fingers.\n"),
    _("halo.pin0.set_touchpad_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.pin0.set_touchpad_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.pin0.get_touchpad_value() \nReturn the 'touch value' of the touchpad.\n"
        "Returns a number of 0-100, the higher the value, the more likely the touchpad is being touched"),
    _("halo.pin0.set_pwm_frequency(frequency) \n"),
    _("halo.pin0.set_pwm_duty(duty) \n"),
    _("halo.pin0.play_note(note, beat = None) \n"),
    _("halo.pin0.play_tone(frequency, time_s = None) \n"),
    _("halo.pin1.write_digital(value) \nOutput digital value to pin\n\nvalue: 0 or 1 number for the output"),
    _("halo.pin1.servo_write(value) \nSet the angle or the servo PWM high pulse length\n\n"
        "value: a number, servo angle for 0-180; high pulse length(us) for 544-20000\n"
        "number between 180 and 544 will be treated as 180"),
    _("halo.pin1.read_analog() \nRead and return the analog value of the pin.\n\n"
        "Returns number 0-3300, the voltage(mv) of the signal"),
    _("halo.pin1.write_analog(value) \nOutput a PWM signal through the pin.\n\nvalue: a 0-1023 number"),
    _("halo.pin1.is_touched() \nReturns true if the pin 0 is touched by fingers.\n"),
    _("halo.pin1.set_touchpad_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.pin1.set_touchpad_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.pin1.get_touchpad_value() \nReturn the 'touch value' of the touchpad.\n"
        "Returns a number of 0-100, the higher the value, the more likely the touchpad is being touched"),
    _("halo.pin1.set_pwm_frequency(frequency) \n"),
    _("halo.pin1.set_pwm_duty(duty) \n"),
    _("halo.pin1.play_note(note, beat = None) \n"),
    _("halo.pin1.play_tone(frequency, time_s = None) \n"),
    _("halo.pin2.write_digital(value) \nOutput digital value to pin\n\nvalue: 0 or 1 number for the output"),
    _("halo.pin2.servo_write(value) \nSet the angle or the servo PWM high pulse length\n\n"
        "value: a number, servo angle for 0-180; high pulse length(us) for 544-20000\n"
        "number between 180 and 544 will be treated as 180"),
    _("halo.pin2.read_analog() \nRead and return the analog value of the pin.\n\n"
        "Returns number 0-3300, the voltage(mv) of the signal"),
    _("halo.pin2.write_analog(value) \Output a PWM signal through the pin.\n\nvalue: a 0-1023 number "),
    _("halo.pin2.is_touched() \nReturns true if the pin 0 is touched by fingers.\n"),
    _("halo.pin2.set_touchpad_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.pin2.set_touchpad_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.pin2.get_touchpad_value() \nReturn the 'touch value' of the touchpad.\n"
        "Returns a number of 0-100, the higher the value, the more likely the touchpad is being touched"),
    _("halo.pin2.set_pwm_frequency(frequency) \n"),
    _("halo.pin2.set_pwm_duty(duty) \n"),
    _("halo.pin2.play_note(note, beat = None) \n"),
    _("halo.pin2.play_tone(frequency, time_s = None) \n"),
    _("halo.pin3.write_digital(value) \nOutput digital value to pin\n\nvalue: 0 or 1 number for the output"),
    _("halo.pin3.servo_write(value) \nSet the angle or the servo PWM high pulse length\n\n"
        "value: a number, servo angle for 0-180; high pulse length(us) for 544-20000\n"
        "number between 180 and 544 will be treated as 180"),
    _("halo.pin3.read_analog() \nRead and return the analog value of the pin.\n\n"
        "Returns number 0-3300, the voltage(mv) of the signal"),
    _("halo.pin3.write_analog(value) \Output a PWM signal through the pin.\n\nvalue: a 0-1023 number "),
    _("halo.pin3.is_touched() \nReturns true if the pin 0 is touched by fingers.\n"),
    _("halo.pin3.set_touchpad_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.pin3.set_touchpad_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.pin3.get_touchpad_value() \nReturn the 'touch value' of the touchpad.\n"
        "Returns a number of 0-100, the higher the value, the more likely the touchpad is being touched"),
    _("halo.pin3.set_pwm_frequency(frequency) \n"),
    _("halo.pin3.set_pwm_duty(duty) \n"),
    _("halo.pin3.play_note(note, beat = None) \n"),
    _("halo.pin3.play_tone(frequency, time_s = None) \n"),
    # speech recognition
    _("halo.speech_recognition.start(server = halo.speech_recognition.SERVER_MICROSOFT, language = halo.speech_recognition.LAN_CHINESE, time_s = 5, wait_flag = True) \n"),
    _("halo.speech_recognition.begin(time_s = 3,  language = 'mandarin') \nlan:'mandarin'/'cantonese'/'mandarin_taiwan'/'english'/'French'/'German'/'italian'/'spanish'"),
    _("halo.speech_recognition.set_token(server = halo.speech_recognition.SERVER_MICROSOFT, token) \n"),
    _("halo.speech_recognition.set_access_token(token) \n"),
    _("halo.speech_recognition.set_token_url(server, url) \n"),
    _("halo.speech_recognition.set_recognition_address(url) \n"),
    _("halo.speech_recognition.get_result_code() \n"),
    # touchpad
    _("halo.touchpad0.is_touched() \nReturn True if the touchpad 0 is touched."),
    _("halo.touchpad0.set_touch_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.touchpad0.set_touch_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.touchpad0.get_value() \n"),
    _("halo.touchpad1.is_touched() \n"),
    _("halo.touchpad1.set_touch_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.touchpad1.set_touch_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.touchpad1.get_value() \n"),
    _("halo.touchpad2.is_touched() \n"),
    _("halo.touchpad2.set_touch_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.touchpad2.set_touch_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.touchpad2.get_value() \n"),
    _("halo.touchpad3.is_touched() \n"),
    _("halo.touchpad3.set_touch_threshold(value) \nSet the threshold of is_touched\n\n"
        "value:a 0-1 number. The closer to 0, the easier for is_touched to return True"),
    _("halo.touchpad3.set_touch_sensitivity(level) \nSet the sensitivity of touch pads.\n\n"
        "level: a string of ['high','middle','low']"),
    _("halo.touchpad3.get_value() \n"),
    # upload_mode_message
    _("halo.upload_mode_message.get_info(msg) \n"),
    _("halo.upload_mode_message.broadcast(message, value = "") \n"),
    # wifi
    _("halo.wifi.is_connected() \n"),
    _("halo.wifi.start(ssid, password) \nStart as STA mode"),
    # speaker
    _("halo.speaker.volume \n"),
    _("halo.speaker.tempo \n"),
    _("halo.speaker.stop_sounds() \n"),
    _("halo.speaker.play_melody_until_done(file_name) \n"),
    _("halo.speaker.play_melody(file_name) \n"),
    _("halo.speaker.play_tone(frequency, time_s = None) \n"),
    _("halo.speaker.play_note(note, beat = None) \n"),
    _("halo.speaker.rest(beat) \n"),
    # motion sensor
    _("halo.motion_sensor.get_roll() \n"),
    _("halo.motion_sensor.get_pitch() \n"),
    _("halo.motion_sensor.get_yaw() \n"),
    _("halo.motion_sensor.get_acceleration(axis) \nx/y/z"),
    _("halo.motion_sensor.get_gyroscope(axis) \nx/y/z"),
    _("halo.motion_sensor.get_rotation(axis) \nx/y/z"),
    _("halo.motion_sensor.reset_rotation(axis = 'all') \nx/y/z/all"),
    _("halo.motion_sensor.is_tilted_left() \n"),
    _("halo.motion_sensor.is_tilted_right() \n"),
    _("halo.motion_sensor.is_arrow_up() \n"),
    _("halo.motion_sensor.is_arrow_down() \n"),
    _("halo.motion_sensor.is_shaked() \n"),
    _("halo.motion_sensor.get_shake_strength() \n"),
    _("halo.motion_sensor.is_led_ring_up() \n"),
    _("halo.motion_sensor.is_led_ring_down() \n"),
    _("halo.motion_sensor.is_free_fall() \n"),
    _("halo.motion_sensor.is_rotate_clockwise() \n"),
    _("halo.motion_sensor.is_rotate_anticlockwise() \n"),
    # event
    _("@event.button_pressed \n"),
    _("@event.shaked \n"),
    _("@event.tilted_left \n"),
    _("@event.tilted_right \n"),
    _("@event.arrow_up \n"),
    _("@event.arrow_down \n"),
    _("@event.free_fall \n"),
    _("@event.rotate_clockwise \n"),
    _("@event.rotate_anticlockwise \n"),
    _("@event.received(message_str) \n"),
    _("@event.cloud_message(message) \n"),
    _("@event.mesh_message(message) \n"),
    _("@event.upload_mode__message(message) \n"),
    _("@event.received(message_str) \n"),
    _("@event.greater_than(threshold, type_str) \n"),
    _("@event.touchpad0_active \n"),
    # Math functions
    _("math.sqrt(x) \nReturn the square root of 'x'."),
    _("math.pow(x, y) \nReturn 'x' raised to the power 'y'."),
    _("math.exp(x) \nReturn math.e**'x'."),
    _("math.log(x, base=math.e) \nWith one argument, return the natural logarithm of 'x' (to base e).\nWith two arguments, return the logarithm of 'x' to the given 'base'."),
    _("math.cos(x) \nReturn the cosine of 'x' radians."),
    _("math.sin(x) \nReturn the sine of 'x' radians."),
    _("math.tan(x) \nReturn the tangent of 'x' radians."),
    _("math.acos(x) \nReturn the arc cosine of 'x', in radians."),
    _("math.asin(x) \nReturn the arc sine of 'x', in radians."),
    _("math.atan(x) \nReturn the arc tangent of 'x', in radians."),
    _("math.atan2(x, y) \nReturn atan(y / x), in radians."),
    _("math.ceil(x) \nReturn the ceiling of 'x', the smallest integer greater than or equal to 'x'."),
    _("math.copysign(x, y) \nReturn a float with the magnitude (absolute value) of 'x' but the sign of 'y'. "),
    _("math.fabs(x) \nReturn the absolute value of 'x'."),
    _("math.floor(x) \nReturn the floor of 'x', the largest integer less than or equal to 'x'."),
    _("math.fmod(x, y) \nReturn 'x' modulo 'y'."),
    _("math.frexp(x) \nReturn the mantissa and exponent of 'x' as the pair (m, e). "),
    _("math.ldexp(x, i) \nReturn 'x' * (2**'i')."),
    _("math.modf(x) \nReturn the fractional and integer parts of x.\nBoth results carry the sign of x and are floats."),
    _("math.isfinite(x) \nReturn True if 'x' is neither an infinity nor a NaN, and False otherwise."),
    _("math.isinf(x) \nReturn True if 'x' is a positive or negative infinity, and False otherwise."),
    _("math.isnan(x) \nReturn True if 'x' is a NaN (not a number), and False otherwise."),
    _("math.trunc(x) \nReturn the Real value 'x' truncated to an Integral (usually an integer)."),
    _("math.radians(x) \nConvert angle 'x' from degrees to radians."),
    _("math.degrees(x) \nConvert angle 'x' from radians to degrees."),

    _("codey.display.show_image(image, x=0, y=0, time_s=1)\ncodey show image at position, for seconds"),
    _("codey.display.clear()\ncodey clear image"),
    _("codey.display.show(text='hello', x=0, y=0, wait=False)\ncodey show text at position"),
    _("codey.display.set_pixel(x=0, y=0, on=True)\ncodey set pixel at position"),
    _("codey.display.toggle_pixel(x=0, y=0)\ncodey toggle pixel at position"),
    _("codey.display.get_pixel(x=0, y=0)\ncodey get pixel at position"),
    _("codey.led\ncodey led module"),
    _("codey.led.show(r=255, g=0, b=0, secs=0)\ncodey led show rgb color for seconds"),
    _("codey.led.set_red(value=255)\nchange codey led red color value"),
    _("codey.led.set_green(value=255)\nchange codey led green color value"),
    _("codey.led.set_blue(value=255)\nchange codey led blue color value"),
    _("codey.led.off()\nturn off codey led"),
    _("rocky.color_ir_sensor\nrocky color_ir_sensor module"),
    _("rocky.set_led_color(color_name='black')\nset rocky led color"),
    _("codey.speaker\ncodey speaker module"),
    _("codey.speaker.play_melody(wav_name, until_done=False)\ncodey speaker play sound"),
    _("codey.speaker.stop_sounds()\ncodey speaker stop sounds"),
    _("codey.speaker.play_note(note=60, beats=0.25)\ncodey speaker play note for beats"),
    _("codey.speaker.rest(beats=0.25)\ncodey speaker rest for beats"),
    _("codey.speaker.play_tone(hz=700, beats=0.25)\ncodey speaker play tone for beats"),
    _("codey.speaker.volume\ncodey speaker volume"),
    _("rocky.forward(speed=50, time=0, straight = True)\nrocky move forward by power for seconds"),
    _("rocky.backward(speed=50, time=0, straight = True)\nrocky move backward by power for seconds"),
    _("rocky.turn_left(speed=50, time=0)\nrocky move turn left by power for seconds"),
    _("rocky.turn_right(speed=50, time=0)\nrocky move turn right by power for seconds"),
    _("rocky.turn_left_by_degree(degree=15)\nrocky turn left by degree until done"),
    _("rocky.turn_right_by_degree(degree=15)\nrocky turn right by degree until done"),
    _("rocky.drive(left=50, right=50)\nrocky move by left and right power"),
    _("rocky.stop()\nrocky stop"),
    _("codey.button_a.is_pressed()\nis codey button a pressed"),
    _("codey.button_b.is_pressed()\nis codey button a pressed"),
    _("codey.button_c.is_pressed()\nis codey button a pressed"),
    _("codey.is_rocky_connected()\nis codey connected rocky?"),
    _("codey.potentiometer.get_value()\ncodey potentiometer value"),
    _("codey.sound_sensor.get_loudness()\ncodey sound sensor loudness"),
    _("codey.light_sensor.get_value()\ncodey light sensor value"),
    _("codey.battery.get_percentage()\ncodey battery percentage"),
    _("codey.motion_sensor.is_shaked()\nis codey shaked?"),
    _("codey.motion_sensor.get_shake_strength()\ncodey shake strength"),
    _("codey.motion_sensor\ncodey motion sensor module"),
    _("codey.motion_sensor.is_tilted_left()\nis codey tilted left?"),
    _("codey.motion_sensor.is_tilted_right()\nis codey tilted right?"),
    _("codey.motion_sensor.is_ears_up()\nis codey ears up?"),
    _("codey.motion_sensor.is_ears_down()\nis codey ears down?"),
    _("codey.motion_sensor.is_display_up()\nis codey display up?"),
    _("codey.motion_sensor.is_display_down()\nis codey display down?"),
    _("codey.motion_sensor.is_upright()\nis codey upright?"),
    _("codey.motion_sensor.get_roll()\ncodey roll degree"),
    _("codey.motion_sensor.get_pitch()\ncodey pitch degree"),
    _("codey.motion_sensor.get_rotation(${1|'x','y','z'|})\ncodey rotation degree"),
    _("codey.motion_sensor.reset_rotation(${1|'x','y','z','all'|})\ncodey reset rotation"),
    _("codey.motion_sensor.get_timer()\ncodey timer"),
    _("rocky.color_ir_sensor.is_obstacle_ahead()\nis rocky obstacle ahead?"),
    _("rocky.color_ir_sensor.is_color(${1|'red','green','blue','yellow','cyan','purple','white'|})\nis rocky detected color?"),
    _("rocky.color_ir_sensor.get_red()\nrocky detected red color value"),
    _("rocky.color_ir_sensor.get_green()\nrocky detected green color value"),
    _("rocky.color_ir_sensor.get_blue()\nrocky detected blue color value"),
    _("rocky.color_ir_sensor.get_light_strength()\nrocky color sensor ambient light intensity"),
    _("rocky.color_ir_sensor.get_reflected_light()\nrocky color sensor reflected light intensity"),
    _("rocky.color_ir_sensor.get_reflected_infrared()\ncolor sensor reflected infrared light intensity"),
    _("rocky.color_ir_sensor.get_greyness()\ncolor sensor grey-scale value"),
    _("codey.ir\ncodey ir module"),
    _("codey.ir.send(msg='A')\ncodey ir send message"),
    _("codey.ir.receive()\ncodey ir received message"),
    _("codey.ir.learn(time_s = 3)\ncodey ir record home appliances remote signal seconds"),
    _("codey.ir.send_learned_result()\ncodey ir send learned result message"),
]
