# PDP8-ES simulator

Simulation of a pdp8 minicomputer running OS/8.
The simulator is designed to run on a ESP32 with OLED and 16MB flash.
The images of an 3 RK05 disks and 2 dectapes are stored into flash partitions of the ESP32.  An SD card is supported to store more images and allow files for the simulated PTR: and PTP: devices.

There is a simpler version in the archive dirrectory that wil run on a bare ESP32 devboard.  An SD card is supported to copy disk images to the flash partitions.

This is a esp-idf project.  Run "make menuconfig" first to configure Wifi settings and the like.

Read the documentation for details.
