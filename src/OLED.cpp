//***************************************************************************************************
//                                   O L E D . C P P                                                *
//***************************************************************************************************
// Driver for SSD1306/SSD1309/SH1106 display                                                        *
//***************************************************************************************************

#include "Wire.h"
#include "OLED.hpp"

extern void dbgprint ( const char* format, ... ) ;

#define OLED_I2C_ADDRESS   0x3C

// Color definitions.  OLED only have 2 colors.
#define BLACK                 0
#define WHITE              0xFF
#define OLED_NPAG             8			// Number of pages

// Control byte
#define OLED_CONTROL_BYTE_CMD_SINGLE    0x80
#define OLED_CONTROL_BYTE_CMD_STREAM    0x00
#define OLED_CONTROL_BYTE_DATA_STREAM   0x40

// Fundamental commands (pg.28)
#define OLED_CMD_SET_CONTRAST           0x81	// follow with 0x7F
#define OLED_CMD_DISPLAY_RAM            0xA4
#define OLED_CMD_DISPLAY_ALLON          0xA5
#define OLED_CMD_DISPLAY_NORMAL         0xA6
#define OLED_CMD_DISPLAY_INVERTED       0xA7
#define OLED_CMD_DISPLAY_OFF            0xAE
#define OLED_CMD_DISPLAY_ON             0xAF
#define OLED_CMD_SCROLL_OFF             0x2E

// Addressing Command Table (pg.30)
#define OLED_CMD_SET_MEMORY_ADDR_MODE   0x20	// follow with 0x00 = HORZ mode = Behave like a KS108 graphic LCD
#define OLED_CMD_SET_COLUMN_RANGE       0x21	// can be used only in HORZ/VERT mode - follow with 0x00 and 0x7F = COL127
#define OLED_CMD_SET_PAGE_RANGE         0x22	// can be used only in HORZ/VERT mode - follow with 0x00 and 0x07 = PAGE7
#define OLED_CMD_SET_PAGE_START_ADDR    0xB0	// Set page start address for page addressing mode
// Hardware Config (pg.31)
#define OLED_CMD_SETLOWCOLUMN           0x00
#define OLED_CMD_SETHIGHCOLUMN          0x10
#define OLED_CMD_SET_STARTLINE          0x40
#define OLED_CMD_SET_MUX_RATIO          0xA8	// follow with 0x3F = 64 MUX
#ifdef ROT180
 #define OLED_CMD_SET_SEGMENT_REMAP     0xA0  // Mirror X
 #define OLED_CMD_SET_COM_SCAN_MODE     0xC0	// Mirror Y
#else
 #define OLED_CMD_SET_SEGMENT_REMAP     0xA1  // Do not mirror X
 #define OLED_CMD_SET_COM_SCAN_MODE     0xC8	// Do not mirror Y
#endif
#define OLED_CMD_SET_DISPLAY_OFFSET     0xD3	// follow with 0x00
#define OLED_CMD_SET_COM_PIN_MAP        0xDA	// follow with 0x12
#define OLED_CMD_NOP                    0xE3	// NOP

// Timing and Driving Scheme (pg.32)
#define OLED_CMD_SET_DISPLAY_CLK_DIV    0xD5	// follow with 0x80
#define OLED_CMD_SET_PRECHARGE          0xD9	// follow with 0xF1
#define OLED_CMD_SET_VCOMH_DESELCT      0xDB	// follow with 0x30

// Charge Pump (pg.62)
#define OLED_CMD_SET_CHARGE_PUMP        0x8D	// follow with 0x14

uint8_t      fillbuf[] = { 0, 0, 0, 0 } ;		  // To clear 4 bytes of SH1106 RAM
uint8_t      initbuf[] =                      // Initial commands to init OLED
            {
              OLED_CONTROL_BYTE_CMD_STREAM,		          // Stream next bytes
              OLED_CMD_DISPLAY_OFF,			                // Display off
              OLED_CMD_SET_DISPLAY_CLK_DIV, 0x80,	      // Set divide ratio
              OLED_CMD_SET_MUX_RATIO, SCREEN_HEIGHT-1,	// Set multiplex ration (1:HEIGHT)
              OLED_CMD_SET_DISPLAY_OFFSET, 0,		        // Set diplay offset to 0
              OLED_CMD_SET_STARTLINE,			              // Set start line address
              OLED_CMD_SET_CHARGE_PUMP, 0x14,		        // Enable charge pump
              OLED_CMD_SET_MEMORY_ADDR_MODE, 0x00,	    // Set horizontal addressing mode
              OLED_CMD_SET_SEGMENT_REMAP,		            // Mirror / don't mirror X
              OLED_CMD_SET_COM_SCAN_MODE,		            // Mirror / don't mirror Y
              OLED_CMD_SET_COM_PIN_MAP, 0x12,		        // Set com pins hardware config
              OLED_CMD_SET_CONTRAST, 0x7F,		          // Set contrast
              OLED_CMD_SET_PRECHARGE, 0x22,		          // Set precharge period, was F1
              OLED_CMD_SET_VCOMH_DESELCT, 0x20,		      // Set VCOMH
              OLED_CMD_DISPLAY_RAM,			                // Output follows RAM
              OLED_CMD_DISPLAY_NORMAL,			            // Set normal color
              OLED_CMD_SCROLL_OFF,			                // Stop scrolling
              OLED_CMD_DISPLAY_ON			                  // Display on
            } ;


//***********************************************************************************************
//                                O L E D constructor                                           *
//***********************************************************************************************
// Constructor for the display.                                                                 *
// Assumes that Wire.begin() as been called.                                                    *
//***********************************************************************************************
OLED::OLED ( const char* d_type, int sda_pin, int scl_pin )		  // Constructor
{
  isSH1106 = ( strncmp ( d_type, "SH", 2 ) == 0 ) ;		          // Get display type
  isSSD1309 = ( strncmp ( d_type, "SSD", 3 ) == 0 ) ;
  Wire.begin ( sda_pin, scl_pin, (uint32_t)400000 ) ;	          // Init I2C
	i2cScan() ;												                            // Test I2C bus
  ssdbuf = (page_struct*) malloc ( 8 * sizeof(page_struct) ) ;	// Create buffer for screen
  clear() ;							                                        // Clear the display
  delay(1500) ; // TEST*TEST*TEST
}


//***********************************************************************************************
//                                O L E D :: D I S P L A Y                                      *
//***********************************************************************************************
// Refresh the display.                                                                         *
// Paramater force will force rewrite of all pages, disregarding dirty.                 	      *
//***********************************************************************************************
void OLED::display ( bool force )
{
  uint8_t          pg ;						                            // Page number 0..OLED_NPAG - 1

  for ( pg = 0 ; pg < OLED_NPAG ; pg++ )                      // Handle all pages
  {
    if ( ssdbuf[pg].dirty || force )				                  // Refresh needed or forced?
    {
      ssdbuf[pg].dirty = false ;				                      // Yes, set page to "up-to-date"
      Wire.beginTransmission ( OLED_I2C_ADDRESS ) ;		        // Open I2C channel
      Wire.write ( (uint8_t)OLED_CONTROL_BYTE_CMD_SINGLE ) ;	// Set single byte command mode
      Wire.write ( (uint8_t)(0xB0 | pg ) ) ;			            // Set page address
      if ( isSH1106 )						                              // Is it an SH1106?
      {
        Wire.write ( (uint8_t)0x00 ) ;				                // Set lower column address to 0
        Wire.write ( (uint8_t)0x10 ) ;				                // Set higher column address to 0
      }
      Wire.endTransmission() ;					                      // End of transmission
      Wire.beginTransmission ( OLED_I2C_ADDRESS ) ;		        // Begin new transmission
      Wire.write ( (uint8_t)OLED_CONTROL_BYTE_DATA_STREAM ) ;	// Set multi byte data mode
      if ( isSH1106 )						                              // Is it a SH1106?
      {
        Wire.write ( fillbuf, 4 ) ;				                    // Yes, fill extra RAM with zeroes
      }
      Wire.write ( ssdbuf[pg].page, 64 ) ;			              // Send 1st half page with data
      Wire.endTransmission() ;					                      // End of transmission
      // Channel is closed and reopened because of limited buffer space
      Wire.beginTransmission ( OLED_I2C_ADDRESS ) ;		        // Begin transmission
      Wire.write ( (uint8_t)OLED_CONTROL_BYTE_DATA_STREAM ) ;	// Set multi byte data mode
      Wire.write ( ssdbuf[pg].page + 64, 64 ) ;			          // Send 2nd half page with data
      Wire.endTransmission() ;					                      // End of transmission
    }
  }
}


//***********************************************************************************************
//                                 O L E D :: C L E A R                                         *
//***********************************************************************************************
// Clear the display buffer and the display.                                                    *
// The display will also be initialized.                                                        *
//***********************************************************************************************
void OLED::clear()
{
  Wire.beginTransmission ( OLED_I2C_ADDRESS ) ;		    // Init, begin transmission
  Wire.write ( initbuf, sizeof(initbuf) ) ;           // Write init buffer
  Wire.endTransmission() ;				                    // End of transmission
  for ( uint8_t pg = 0 ; pg < OLED_NPAG ; pg++ )	    // Handle all pages
  {
    memset ( ssdbuf[pg].page, BLACK, SCREEN_WIDTH ) ;	// Clears all pixels of 1 page
    ssdbuf[pg].rvalue = 0x80000000 ;			            // Set current value of register to 0
  }
  display ( true ) ;
}


//***********************************************************************************************
//                            O L E D P :: S E T M A R K E R S                                  *
//***********************************************************************************************
// Draw lines just above console lights.                                                        *
// The bits in range specify the length of the markers.                                         *
//***********************************************************************************************
void OLED::setmarkers ( uint8_t pg, uint32_t range )
{
  uint8_t  x = 124 ;				              // X-position
  uint32_t mask = 1 ;
  uint8_t  len = 3 ;
  uint8_t* p ;					                  // X-Pointer in right page

  while ( mask & range )
  {
    p = ssdbuf[pg].page + x ;
    for ( uint8_t i = 0 ; i < len ; i++ )	// Draw a line, 3 or 6 pixels
    {
      *p++ = 1 << 1 ;				              // Set single bit to draw hor. line
    }
    len = 6 ;
    if ( mask & 0444444 )			            // Time to draw some space?
    {
      x -= 2 ;				                    // Yes
      len = 3 ;
    }
    x -= 6 ;
    mask = mask << 1 ;
  }
  ssdbuf[pg].dirty = true ;			          // Page is dirty now
}


//***********************************************************************************************
//                              O L E D :: S H O W _ R E G I S T E R                            *
//***********************************************************************************************
// Set register to the console lights.                                                          *
// The bits in range specify the length of the markers.                                         *
//***********************************************************************************************
void OLED::show_register ( uint8_t pg, uint32_t range, uint32_t r )
{
  uint32_t mask = 1 ;
  uint8_t  x = 124 ;
  uint8_t  b ;				                  // Bitpattern for one light
  uint8_t* p ;				                  // X-Pointer in right page

  if ( r != ssdbuf[pg].rvalue )         // Register changed?
  {
    while ( mask & range )
    {
      p = ssdbuf[pg].page + x ;		      // Position in page
      b = *p & 7 ;			                // Do not touch markers
      if ( r & mask )			              // Light for this bit?
      {
        b |= ( 7 << 3 ) ;		            // Light on, heigth is 3
      }
      *p++ = b ;			                  // Set 3 pixels vertical
      *p++ = b | 32 ;			              // Another 3 pixels vertical, middle bit also set for "0"
      *p   = b ;			                  // And the last 3 bits vertical
      if ( mask & 0444444 )
      {
        x -= 2 ;
      }
      x -= 6 ;
      mask = mask << 1 ;
    }
    ssdbuf[pg].dirty = true ;		        // Set page to modified
    ssdbuf[pg].rvalue = r ;		          // For next compare
  }
}


//******************************************************************************************
//                               O L E D :: I 2 C S C A N                                  *
//******************************************************************************************
// Scan I2C bus for devices.                                                               *
//******************************************************************************************
bool OLED::i2cScan()
{
  static bool    i2cfound = false ;						      // True if at least one I2C device found

  dbgprint ( "Scan I2C bus.." ) ;						        // Info with sequence number
  for ( uint8_t i = 8 ; i < 120 ; i++ )					    // I2Cdetect
  {
    Wire.beginTransmission ( i ) ;						      // Begin I2C transmission Address (i)
    if ( Wire.endTransmission () == 0 )					    // Receive 0 = success (ACK response) 
    {
      dbgprint ( "Found I2C address 0x%02X", i ) ;	// Show detected I2C address
      i2cfound = true ;									            // Remember at least found one
    }
  }
  if ( ! i2cfound )
  {
    dbgprint ( "No I2C devices found" ) ;
  }
  return i2cfound ;
}

