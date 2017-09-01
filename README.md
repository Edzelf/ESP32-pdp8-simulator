# pdp8 simulator

Simulation of a pdp8 minicomputer running OS/8.
The simulator is designed to run on a ESP32.
The images of an RK08 disk, 2 dectapes, an RX01 floppy disk are stored into flash partitions of the ESP32.

The simplest version wil run on a bare ESP32 devboard.  An SD card is supported to copy disk images to the flash partitions.

This is a esp-idf project.  Run "make menuconfig" first to configure Wifi settings and the like.
