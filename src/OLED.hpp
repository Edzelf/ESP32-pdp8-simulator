//***************************************************************************************************
//                                   O L E D . H P P                                                *
//***************************************************************************************************
// Driver for SSD1306/SSD1309/SH1106 display                                                        *
//***************************************************************************************************
#include <Arduino.h>
#include <string.h>

#define SCREEN_WIDTH        128                    // OLED display width, in pixels
#define SCREEN_HEIGHT        64                    // OLED display height, in pixels
#define ROT180                                     // Undefine for no rotation

// Color definitions.  OLED has 2 colors.
#define BLACK                 0
#define WHITE              0xFF
#define OLED_NPAG             8                    // Number of pages (text lines)

// Data to display.
struct page_struct
{
  uint8_t   page[128] ;                             // Buffer for one page (8 pixels heigh)
 	uint32_t  rvalue ;                                // Contents of the simulated PDP8 register
  bool      dirty ;                                 // True if modified
} ;

class OLED
{
  public:
              OLED ( const char* d_type, int sda_pin,     // Constructor
                     int scl_pin ) ;
    void      clear() ;                                   // Clear buffer
    void      display ( bool force = false ) ;            // Display buffer
    void      setmarkers ( uint8_t pg, uint32_t range ) ;
    void      show_register ( uint8_t pg, uint32_t range,
                              uint32_t r ) ;
    bool      i2cScan() ;                                 // Scan I2C bus
  private:
    bool                    isSH1106 = false ;            // Display is a SH1106
    bool                    isSSD1309 = false ;           // Display is a SSD1309 or not
    struct page_struct*     ssdbuf = NULL ;
} ;
