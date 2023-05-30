// config.h
// Some definitions for the used hardware
// Note that the flash size (4 or 16 MB) should be configured in platformio.ini!

#define WIFI_SSID     "SSID-11"               // Enter your WiFi credentials here
#define WIFI_PASSWORD "PWC0DE11"
#define TIMEZONE      "CET-1CEST-2,M3.5.0/02:00:00,M10.5.0/03:00:00"      // Time zone Europe/Amsterdam
//#define TIMEZONE "NZST-12NZDT-13,M10.1.0/02:00:00,M3.3.0/03:00:00"      // Timezone for New Zealand

#define OLEDDISPLAY                         // OLED support
#define OTA                                 // OTA support

#define TTGO_OLED                           // Wemos® TTGO ESP32 18650 Battery Holder + 0.96Inch OLED

#define SD_MOSI     23
#define SD_MISO     19
#define SD_SCK      18
#define SD_CS        5                      // CS pin for SD card

#ifdef TTGO_OLED
  #define SDA_PIN      5
  #define SCL_PIN      4
  #define RST_PIN     -1                    // Not used
#else
  #define SDA_PIN      4
  #define SCL_PIN     15
  #define RST_PIN     16
#endif


