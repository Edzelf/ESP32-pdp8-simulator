//***********************************************************************************************
//*					PDP8 simulator for ESP32.													                                  *
//*					By Ed Smallenburg, august 2017.												                              *
//***********************************************************************************************
//* Uses wear-leveling library for simulation of storage devices like RK08, DECtape.			      *
//* Communications (TTY simulation) is handled trough a Telnet session (client like PuTTY).		  *
//* Note that bitnumber in the comments refer to the PDP numbering scheme:						          *
//*     0  1  2  3  4  5  6  7  8  9 10 11		Example for a memory reference instruction.		    *
//*   +--+--+--+--+--+--+--+--+--+--+--+--+														                          *
//*   | opcode |     o p e r a n d        |														                          *
//*   +--+--+--+--+--+--+--+--+--+--+--+--+														                          *
//* The interrupt system is not yet implemented.												                        *
//***********************************************************************************************
// Version history:																				                                      *
// 26-AUG-2017, ES	First set-up																                                *
// 04-SEP-2017, ES	Correction keyboard input and fake-drivers.									                *
// 11-OCT-2017, ES	Correction default date.													                          *
// 15-JAN-2018, ES	Version for ESP module with 0.96 inch OLED and 128 Mbit flash.				      *
// 16-JAN-2018, ES	OTA update of application software.											                    *
// 19-AUG-2020, ES  Changed some include files to get rid of errors/warning.					          *
// 07-SEP-2022, ES  Switched to Arduino platform												                        *
// 27-SEP-2022, ES  Minor corrections.															                            *
// 24-MAY-2023, ES  Allow ESP to expose an AP if connection to local network fails.             *
// 25-MAY-2023, ES  Show link on display.  Correction time zone.                                *
// 30-MAY-2023, ES  Control of simulator by both serial and telnet.                             *
//***********************************************************************************************
//
#include <Arduino.h>
#include "config.h"							                  // Configuration file
#include <Wire.h>
#include <time.h>
#include <esp_sntp.h>
//#include <esp_task_wdt.h>
#include <WiFi.h>
#include <ArduinoOTA.h>
#include <string.h>
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdarg.h>
#include <esp_partition.h>
#include <SPI.h>
#include <SD.h>
#include <FS.h>
#include <wear_levelling.h>
#include <lwip/err.h>
#include <lwip/sockets.h>
#include <lwip/sys.h>
#include <lwip/netdb.h>

// If OLEDDISPLAY is defined (in config.h), a life front panel is simulated (I2C).
#ifdef OLEDDISPLAY
  #include "OLED.hpp"
#endif
// Port for the telnet server
#define TELNET_PORT 23
// Size of RKA0 / RKBO / DECTAPE / FLOPPY in OS/8 blocks
#define DSKSIZE 3248
#define TAPESIZE 737
#define FLOPSIZE 494

#define NAME "PDP8_ES_01"								      // Project name, host name
#define DEBUG_BUFFER_SIZE 100

// Global variables
bool              DEBUG = true ;              // Debugging on/off
bool              ota_enabled = false ;
SemaphoreHandle_t	dbgsem = NULL ;						  // For exclusive usage of dbgprint
struct tm			    timeinfo = { 0 } ;					// Current time
int               lc_main= 0 ;						    // Loop count main loop
TaskHandle_t		  th_telnet ;							    // Task handle for telnet task
int               lc_telnet = 0 ;						  // Loop counter telnet task
TaskHandle_t		  th_sim ;							      // Task handle for simulator task
int               lc_sim = 0 ;						    // Loop counter simulator task
TaskHandle_t		  th_user ;							      // Task handle for user input/output task
int               lc_user = 0 ;						    // Loop counter simulator task
#ifdef OLEDDISPLAY
  TaskHandle_t		th_console ;						    // Task handle for console task
  int				      lc_console = 0 ;					  // Loop counter console task
  OLED*           display = NULL ;            // Will point to OLED object
#endif

uint16_t MEM [8][4096] ;								      // PDP8 32 kw memory stack

uint16_t*			wrdbuf = &MEM[7][0] ;				    // Buffer for 256 PDP8 words for download
														                  // shared with 32 kw memory
uint16_t			os8date ;							          // Date in OS/8 form mmmmdddddyyy
uint16_t			os8datex ;							        // Extended year bits yy0000000

// The event group allows multiple bits for each event, but we only care about one event:
// are we connected to the AP with an IP?
const int			CONNECTED_BIT = 0x00000001 ;
//
// Variables for emulator.
uint16_t PC = 07600 ;									// Program counter
uint16_t AC = 0 ;										  // Accumulator
uint16_t MA = 0 ;										  // Memory address buffer
uint16_t MB = 0 ;										  // Memory buffer
uint16_t MQ = 0 ;										  // Multiplier/Quotient register
uint16_t IR = 0 ;										  // Instruction register (=MEM[IF][PC])
uint16_t SR = 07600 ;									// Switch register
bool     IENA = false ;								// Interrupt enable register
bool     IENApending = false ;				// IE pending during one instruction
uint16_t DF = 0 ;										  // Data field
uint16_t IF = 0 ;										  // Instruction field
uint16_t IFpending = 0 ;							// IF after next JMP/JMS
uint16_t SF = 0 ;										  // Save field register, set by interrupt
bool     running = false ;						// Not running yet
uint32_t instcount = 0 ;							// Count number of emulated instructions
bool     flushrequest = false ;				// Request flag for flush
bool     uppercase = false ;					// Convert input chars to Upper case
char     PTRfile[100] ;								// Input file for simulated PTR
FILE*    PTRhandle = NULL ;						// Handle for open PTR file
uint16_t PTRchar ;										// Next input character
bool     PTReof ;										  // Flag for time-out detection
char     PTPfile[100] ;								// Output file for simulated PTP
FILE*    PTPhandle = NULL ;						// Handle for open PTP file
//
uint16_t t ;											    // Temporary storage

// Structure and data for disk cache, 1 sector = 4096 bytes, 21 PDP8 pages of 128 words.
// So a sector in flash is filled with 21 * 128 * 1.5 = 4032 bytes.
// An RKA0/RKB0 disk is 6496 pages, so a partition for this should be at least 6496 / 21 = 310 sectors.
// A DECtape is 1474 pages, so a partition for this should be 1474 / 21 = 71 sectors.
// An RX01 floppy disk is 988 pages, so a partition for this should be 988 / 21 = 48 sectors
#define CACHESIZE 16
#define PPS       21
#define ILLHANDLE 0xFFFFFFFF
typedef struct
{
	uint16_t    cbuf[PPS*128] ;							// PDP8 pages, is about 1 sector of flash
	uint32_t    soffset ;								    // Offset in partition for loaded sector
	wl_handle_t handle ;								    // Handle of partition if occupied, otherwise ILLHANDLE
	uint32_t    atime ;									    // Serial number to detect least recently used
	bool        dirty ;									    // True if sector has to be written to flash
}  dcache_t ;
// Define number of sectors to cache, blocks (of 256 PDP8 words) per sector
dcache_t*  dcache[CACHESIZE] ;					  // The sectors to cache
uint16_t   sectorbuf[2048] ;							// 1 flash sector, 2688 words packed in 4096 bytes
uint32_t   atime = 0 ;									  // Serial for detection of least recently used

// Simulated driver for RKA0 Starts at 07607.  This is a copy of the fake handler.
// It does not harm on an OS/8 with the fake handler installed, but it is vital to include
// the fake handler to boot a system without it.
#define SZSYSHND 32										    // 10 handlers, max. 135 octal locations
uint16_t ddr[SZSYSHND] =
{
		/* 7607 */    07402,  //  HND1,	HLT				  / SYS and RKA0 handler
		/* 7610 */    07300,  //		    CLA CLL
		/* 7611 */    01207,  //		    TAD HND1	  / POINTER to parameters
		/* 7612 */    06770,  //		    6770			  / SIMULATES RKA0:
		//					          //		No return here, driver will return to caller directly
		/* 7613 */    07402,  //  HND2,	HLT				  / RKB0 handler
		/* 7614 */    07300,  //		    CLA CLL
		/* 7615 */    01213,  //		    TAD HND2		/ POINTER to parameters
		/* 7616 */    06771,  //		    6771			  / SIMULATES RKB0:
		//					  //		No return here, driver will return to caller directly
		/* 7617 */    07402,  //  HND3,	HLT				  / RKA1 handler
		/* 7620 */    07300,  //		    CLA CLL
		/* 7621 */    01217,  //		    TAD HND3		/ POINTER to parameters
		/* 7622 */    06772,  //		    6772			  / SIMULATES RKA1:
		//					          //		No return here, driver will return to caller directly
		/* 7623 */    07402,  //  HND4,	HLT				  / RKB1 handler
		/* 7624 */    07300,  //		    CLA CLL
		/* 7625 */    01223,  //		    TAD HND4		/ POINTER to parameters
		/* 7626 */    06773,  //		    6773			  / SIMULATES RKB1:
		//					          //		No return here, driver will return to caller directly
		/* 7627 */    07402,  //  HND5,	HLT				  / RKA2 handler
		/* 7630 */    07300,  //		    CLA CLL
		/* 7631 */    01227,  //		    TAD HND5		/ POINTER to parameters
		/* 7632 */    06774,  //		    6774			  / SIMULATES RKA2:
		//					          //		No return here, driver will return to caller directly
		/* 7633 */    07402,  //  HND6,	HLT				  / RKB2 handler
		/* 7634 */    07300,  //		    CLA CLL
		/* 7635 */    01233,  //		    TAD HND6		/ POINTER to parameters
		/* 7636 */    06775,  //		    6775			  / SIMULATES RKB2:
		//					          //		No return here, driver will return to caller directly
		/* 7637 */    07402,  //  HND7,	HLT				  / DTA0 handler
		/* 7640 */    07300,  //		    CLA CLL
		/* 7641 */    01237,  //		    TAD HND7		/ POINTER to parameters
		/* 7642 */    06776,  //		    6776			  / SIMULATES DTA0:
		//					          //		No return here, driver will return to caller directly
		/* 7643 */    07402,  //  HND8,	HLT				  / DTA1 handler
		/* 7644 */    07300,  //		    CLA CLL
		/* 7645 */    01243,  //		    TAD HND8		/ POINTER to parameters
		/* 7646 */    06777,  //		    6777			  / SIMULATES DTA1:
		//					          //		No return here, driver will return to caller directly
} ;

// Common data for the telnet server and console handling. 8 devices
#define NUMDEV 8
typedef struct
{
	char		    devname[4+1] ;							// Device name/partition name plus delimiter
	wl_handle_t	handle ;								    // Handle of partition simulating this device
	uint16_t	  size ;									    // Size in OS/8 blocks
	char		    extension[5+1] ;						// Extension for images on SD card
	uint16_t    offset ;								    // Offset in image file
	bool		    istape ;								    // True for special handling of DECtape files
} devinfo_t ;

// Info about the peripheral devices  RKA0/RKB0 must be entry 0 and 1.  Sequence must be the same as
// the "super" IOTs 6770..6777.
	devinfo_t		devicesx[NUMDEV] =
				{
		/* 0 */		{ "RKA0", 0, DSKSIZE,  ".rk05", 0,       false },	// Combined with RKB0
		/* 1 */ 	{ "RKB0", 0, DSKSIZE,  ".rk05", DSKSIZE, false },	// Combined with RKA0
		/* 2 */		{ "RKA1", 0, DSKSIZE,  ".rk05", 0,       false },	// Combined with RKB1
		/* 3 */ 	{ "RKB1", 0, DSKSIZE,  ".rk05", DSKSIZE, false },	// Combined with RKA1
		/* 4 */		{ "RKA2", 0, DSKSIZE,  ".rk05", 0,       false },	// Combined with RKB2
		/* 5 */ 	{ "RKB2", 0, DSKSIZE,  ".rk05", DSKSIZE, false },	// Combined with RKA2
		/* 6 */ 	{ "DTA0", 0, TAPESIZE, ".tu56", 0,       true  },
		/* 7 */		{ "DTA1", 0, TAPESIZE, ".tu56", 0,       true  },
				};

int				    clientSock = -1 ;						                // Client socket
QueueHandle_t	kbd_queue ;								                  // Queue for telnet input (keystrokes)
QueueHandle_t	tls_queue ;								                  // Queue for telnet output (print)
uint8_t			  kbd_last = 0 ;							                // Last character seen
bool			    kbd_flag = false ;						              // Character available
bool			    abortf = false ;						                // Flag to abort telnet and ESP
uint16_t		  seldev = 0 ;							                  // Selected device (RKA0) for load/save image

enum { IDLE, START, WAIT_ANY, WAIT_CMD } menu_state = IDLE ;	  // State of menu

// Data for SD card
bool				  card_okay ;			                            // True if a good card inserted

bool          apmode = true ;									            // Assume no local network

// Forward declarations
void boot() ;
void flushcache() ;
bool writesec ( uint16_t inx, bool ffree ) ;
bool dskread  ( wl_handle_t handle, uint16_t* wbuf, uint16_t blocknr, uint16_t npages ) ;
bool dskwrite ( wl_handle_t handle, uint16_t* wbuf, uint16_t blocknr, uint16_t npages ) ;

//**************************************************************************************************
//                                          D B G P R I N T                                        *
//**************************************************************************************************
// Send a line of info to serial output.  Works like vsprintf(), but checks the DEBUG flag.        *
// Debug lines will be added to dbglines, a buffer holding the last debuglines.                    *
// Print only if DEBUG flag is true.                                                               *
//**************************************************************************************************
void dbgprint ( const char* format, ... )
{
  static char sbuf[DEBUG_BUFFER_SIZE] ;					    // For debug lines
  va_list     varArgs ;									            // For variable number of params
  char*       p = sbuf + 11 ;							          // Place for formatted string

  if ( xSemaphoreTake ( dbgsem, 200 ) != pdTRUE  )	// Claim resource
  {
    return ;											                  // Not available
  }
  if ( apmode || timeinfo.tm_year <= 0 )				    // Time available?
  {
    strcpy ( sbuf, "D: " ) ;							          // No, no time in debug lines
	p = sbuf + 3 ;										                // Change place for formatted string
  }
  else
  {
    getLocalTime ( &timeinfo ) ;						        // Yes, get local time
    sprintf ( sbuf, "%02d:%02d:%02d - ",				    // Print prefix (time of day)
              timeinfo.tm_hour,
              timeinfo.tm_min,
              timeinfo.tm_sec ) ;
  }
  va_start ( varArgs, format ) ;						        // Prepare parameters
  vsnprintf ( p, sizeof(sbuf) - 11,						      // Format the message
              format, varArgs ) ;
  va_end ( varArgs ) ;									            // End of using parameters
  if ( DEBUG )											                // DEBUG on?
  {
	Serial.print ( "\x1B[32m") ;						          // Green color
    Serial.println ( sbuf ) ;							          // Print the info
	Serial.print ( "\x1B[39m") ;						          // Default color
  }
  xSemaphoreGive ( dbgsem ) ;							          // Release resource
}


//******************************************************************************************
//                                  I 2 C S C A N                                          *
//******************************************************************************************
// Scan I2C bus for devices.                                                               *
//******************************************************************************************
bool i2cScan()
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


//***********************************************************************************************
//									                C L I E N T S E N D     									                  *
//***********************************************************************************************
// Send character data to client if open.  Otherwise to serial.                                 *
//***********************************************************************************************
void clientSend ( const char* p, size_t size  )
{
  if ( clientSock >= 0 )                            // TelNet socket opened?
  {
    if ( send ( clientSock, p, size,                // Yes, send to telnet client
                MSG_DONTWAIT ) < 0 )
    {
      dbgprint ( "Send error!" ) ;						      // Error detected
    }
  }
  else
  {
    Serial.write (p, size ) ;                       // Telnet socket not open, send to serial
  }
}


//***********************************************************************************************
//									                C L I E N T R E C V     									                  *
//***********************************************************************************************
// Read character data from telnet client if open.  Otherwise from serial.                      *
// returns -1 on close connnection, 0 on no input.                                              *
//***********************************************************************************************
int clientRecv ( char* buf, size_t size )
{
  size_t n = 0 ;                                            // Number of characters read

  if ( clientSock >= 0 )                                    // TelNet socket opened?
  {
		n = recv ( clientSock, buf, size, MSG_DONTWAIT ) ;      // Yes, read from telnet socket
    if ( n == 0 )                                           // 0 is disconnect, return -1
    {
			dbgprint ( "Connection closed" ) ;
      clientSock = -1 ;
      n = -1 ;
    }
    if ( n == -1 )                                          // -1 is no input, return 0
    {
      n = 0 ;
    }
  }
  else
  {
    if ( Serial.available() )                               // Prevent long wait in readBytes
    {
      n = Serial.readBytes ( buf, size ) ;                  // No, read from serial input
    }
  }
  return n ;
}


//***********************************************************************************************
//									                K B D _ A V A I L A B L E									                  *
//***********************************************************************************************
// Check the availability of keyboard input.													                          *
//***********************************************************************************************
bool kbd_available()
{
	uint8_t k ;										                // Input from queue

	if ( !kbd_flag )								              // Software flag set?
	{
		if ( uxQueueMessagesWaiting ( kbd_queue ) )	// No, new character arrived?
		{
			xQueueReceive ( kbd_queue, &k, 0 ) ;	    // Yes, read the new character
			kbd_last = k ;							              // Remember as last char
			kbd_flag = true 	;					              // and flag
		}
	}
	return kbd_flag ;								              // Return the flag
}


//***********************************************************************************************
//									                    K B D _ I N P U T											                  *
//***********************************************************************************************
// Get the last keyboard input character.														                            *
//***********************************************************************************************
uint8_t kbd_input()
{
	return kbd_last ;								// Return last read character to caller
}


//***********************************************************************************************
//									                    K B D _ C L E A R											                  *
//***********************************************************************************************
// Emulation of KCC instruction.																                                *
//***********************************************************************************************
void kbd_clear()
{
	kbd_flag = false ;
}


//***********************************************************************************************
//									                      K B D _ G E T												                  *
//***********************************************************************************************
// Get the last keyboard input character and clear the ready_flag.								              *
//***********************************************************************************************
uint8_t kbd_get()
{
	kbd_flag = false ;								    // Clear flag
	return kbd_last ;								      // Return last read character to caller
}


//***********************************************************************************************
//									                  T L S _ S P A C E											                    *
//***********************************************************************************************
// See if there is space in the output queue.													                          *
//***********************************************************************************************
bool tls_space()
{
	return ( uxQueueSpacesAvailable ( tls_queue ) > 0 ) ;	// True if space available
}


//***********************************************************************************************
//									                    T L S _ P U T												                    *
//***********************************************************************************************
// Send a character to the telnet client.														                            *
//***********************************************************************************************
void tls_put ( uint8_t c )
{
	if ( tls_space() )									                          // Do we have space for output?
	{
		xQueueSend ( tls_queue, &c, 1 ) ;				                    // Send to output queue
	}
	else
	{
		dbgprint ( "TLS queue full, ignore character %03o", c ) ;
	}
}


//***********************************************************************************************
//										                  S T R _ P U T											                      *
//***********************************************************************************************
// Send a formatted string to the telnet client.												                        *
// Used by the menu program.																                                    *
//***********************************************************************************************
const char* str_put ( const char* format, ... )
{
	static char sbuf[100] ;								          // For output lines
	va_list     varArgs ;								            // For variable number of parameters
	const char* p = sbuf ;								          // Points to resulting string

	va_start ( varArgs, format ) ;						      // Prepare parameters
	if ( strlen ( format ) < sizeof(sbuf) )
	{
		vsnprintf ( sbuf, sizeof(sbuf), format,			  // Format the message
				        varArgs ) ;
	}
	else
	{
		p = format ;									                // Too long to buffer
	}
	va_end ( varArgs ) ;								            // End of using parameters
  clientSend ( p, strlen ( p ) ) ;        			  // Send to telnet client
	vTaskDelay ( 1 / portTICK_PERIOD_MS ) ;			    // Allow actual transfer to client
	return p ;											                // Return pointer to formatted string
}


//***********************************************************************************************
//											                    C _ P U T											                      *
//***********************************************************************************************
// Send a character to the telnet client.														                            *
// Used by the menu program.																                                    *
//***********************************************************************************************
void c_put ( char c )
{
	clientSend ( &c, 1 ) ;              					// Send to telnet client
}

//***********************************************************************************************
//	  								                S E N D H T T P 											                    *
//***********************************************************************************************
// Send a string to the http client socket (download).											                    *
//***********************************************************************************************
bool sendhttp ( int sock, const char* p )
{
	return ( write ( sock, p, strlen ( p ) ) >= 0 ) ;
}


//***********************************************************************************************
//									                    D O W N L O A D												                  *
//***********************************************************************************************
// Download an image from the internet and store it on RKA0/RKB0 (device 0 and 1).				      *
// This allows an ESP32 to run the simulator without an SD card.								                *
//***********************************************************************************************
void download ( const char* url )
{
	char*				p ;									            // Pointer in url
	char				host[50] ;							        // Hostname from url
	char				spec[80] ;							        // Page/file specification from url
	int					err ;								            // Error code from getaddrinfo
	const struct		addrinfo hints =   {				// Socket parameters
							.ai_family = AF_INET,
							.ai_socktype = SOCK_STREAM } ;
	struct addrinfo*	res ;
	int					s ;									            // Socket handle
	int					rqbytes ;							          // Number of bytes requested
	int					rbytes ;							          // Number of bytes received
	char				recv_buf[64] ;						      // Buffer to receive header lines
	int					filesz = 0 ;						        // Size of file to download
	int                 fileblocks ;						// Site of file in blocks
	int					dlleng = 0 ;						        // Number of bytes downloaded
	int					inx ;								            // Index in recv_buf/dwlbuf
	int					bcnt = 0 ;							        // Block count
	int					timeout = 0 ;						        // Timeout counter for receive
	bool				dskres ;							          // Result of disk write
	bool				getres ;							          // Result of GET request
	uint8_t*			bbuf = (uint8_t*)wrdbuf ;			// Byte pointer in wrdbuf

	strncpy ( host, url, sizeof(host) ) ;				// Copy the host plus garbage
	p = strstr ( url, "/" ) ;								    // Search for spec
	if ( p == NULL )										        // Slash should be there
	{
		return ;											            // Problem
	}
	strncpy ( spec, p, sizeof(spec)  ) ;				// Isolate page/file specification
	p = strstr ( host, "/" ) ;								  // Search for spec
	*p = '\0' ;												          // Delimeter for host
	dbgprint ( "GET %s from %s",
			   spec, host ) ;
	err = getaddrinfo ( host, "80", &hints, &res ) ;		  // Get IP of host
	if ( err != 0 || res == NULL )
	{
		str_put ( "DNS lookup failed err=%d res=%p",
				  err, res ) ;
		return ;
	}
	s = socket ( res->ai_family, res->ai_socktype, 0 ) ;	// Allocate socket
	if ( s < 0 )
	{
		str_put ( "...Failed to allocate socket." ) ;
		freeaddrinfo ( res ) ;
		return ;
	}
	if ( connect ( s, res->ai_addr, res->ai_addrlen ) != 0 )
	{
		str_put ( "... socket connect failed errno=%d", errno ) ;
		close ( s ) ;
		freeaddrinfo ( res ) ;
		return ;
	}
	freeaddrinfo ( res ) ;
	getres = sendhttp ( s, "GET " ) && 					      // Send GET command to host
			 sendhttp ( s, spec ) &&
			 sendhttp ( s, " HTTP/1.1\r\n"
							 "Host: ") &&
			 sendhttp ( s, host ) &&
			 sendhttp ( s, "\r\n"
					 	 	 "User-Agent: esp-idf/1.0 esp32\r\n"
					 	 	 "Connection: close\r\n\r\n" ) ;
	if ( !getres )
	{
		str_put ( "... socket send failed" ) ;
		close ( s) ;
		return ;
	}
	// Read HTTP response
	inx = 0 ;
	while ( true )											              // Read HTTP response lines
	{
		rbytes = read ( s, &recv_buf[inx], 1 ) ;			  // Get one character
		if ( rbytes > 0 )
		{
			if ( recv_buf[inx] == '\r' )					        // Ignore CR
			{
				continue ;
			}
			else if ( recv_buf[inx] == '\n' )				      // LineFeed?
			{
				recv_buf[inx] = '\0' ;						          // Yes, store delimeter
				if ( inx == 0 )								              // Empty line?
				{
					break ;									                  // End of header
				}
				str_put ( "%s\r\n", recv_buf ) ;			      // Show to user
				if ( strstr ( recv_buf,
							  "Content-Length: " ) )
				{
					filesz = atoi ( recv_buf + 16 ) ;		      // Get length in bytes
				}
				inx = 0 ;									                  // Start new line
				continue ;
			}
			inx++ ;
		}
	}
	dbgprint ( "Downloading %d bytes.. ", filesz ) ;
	fileblocks = filesz / 512 ;								        // Compute number of blocks
	str_put ( "Downloading %d bytes, "						    // Show info
			"%d blocks. "
			"This may take a while...\r\n",
			filesz, fileblocks ) ;
	rqbytes = 512 ;											              // Try to read full buffer (1 block)
	for ( int i = 0 ; i < fileblocks / 100 ; i++ )		// Show the number of expected dots
	{
		str_put ( "=" ) ;
	}
	str_put ( "\r" ) ;										            // Dots will overwrite '='
	inx = 0 ;												                  // Offset in buffer
	while ( dlleng < filesz )								          // Read disk image from server
	{
		vTaskDelay ( 10 / portTICK_PERIOD_MS ) ;			  // Allow some time between chunks
		rbytes = read ( s, bbuf + inx, rqbytes ) ;			// Read till end of wrdbuf
		dlleng += rbytes ;									            // Update number of bytes read sofar
		if ( rbytes == rqbytes )							          // Buffer completely filled?
		{
			if ( bcnt < DSKSIZE )							            // RKA0: fully filled?
			{
			  dskres = dskwrite ( devicesx[0].handle,		  // No, write to RKA0:
					  	  	  	  wrdbuf,
								  bcnt, 2 ) ;				                // Write 2 pages to disk
			}
			else
			{
			  dskres = dskwrite ( devicesx[1].handle,		  // No, write to RKB0:
					  	  	  	  wrdbuf,
								  bcnt - DSKSIZE, 2 ) ;		          // Write 2 pages to disk
			}
			if ( !dskres )									              // Check status
			{
				break ;										                  // Error, end download
			}
			bcnt++ ;										                  // Count blocks
			if ( ( bcnt % 100 ) == 0 )						        // Show activity
			{
				str_put ( "." ) ;
			}
			rqbytes = 512 ;									              // For next block
			inx = 0 ;
		}
		else if ( rbytes )									            // Not a full block received
		{
			timeout = 0 ;									                // Activity, so no timeout
			rqbytes -= rbytes ;								            // Adjust number of bytes to read
			inx += rbytes ;									              // New offset in wrdbuf
		}
		else												                    // Zero bytes received
		{
			vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;		  // Allow some time between chunks
			if ( ++timeout >= 100 )							          // More than 10 seconds idle?
			{
				break ;										                  // Yes, give up
			}
		}
	}
	if ( dlleng == filesz )									          // Download complete?
	{
		str_put ( "\r\nDownload completed\r\n" ) ;			// Yes, show the good news
		flushcache() ;										              // Force actual write
	}
	else
	{
		str_put ( "\r\nError downloading image!\r\n" ); // Show error
	}
	close ( s ) ;
}


//***********************************************************************************************
//								              S E A R C H _ S D _ D I R										                    *
//***********************************************************************************************
// Search for a file on SD card depending on extension and sequence.							              *
// If extension is "*", files with all extensions are included.									                *
//***********************************************************************************************
char* search_sd_dir ( const char* ext, uint16_t seq )
{
	File			root ;									        // Work directory
	File			file ;									        // File in work directory
	struct dirent	*dent ;									    // Directory entry structure
	uint16_t		i = 0 ;									      // Sequence nr found
	static char		lstr[50] ;								  // Space for formatted string
	char*			res = NULL ;							      // Function result

	root = SD.open ( "/" ) ;
	if ( root )
	{
		file = root.openNextFile() ;
		while ( file )										      // Find files in directory
		{
			if ( ( strstr ( ext, "*" ) ) ||				// All extensions?
				 ( strstr ( file.path(), ext ) ) )	// or requested extension?
			{
				if ( i == seq )								      // Requested sequence nr?
				{
					strcpy ( lstr, file.path() ) ;		// Copy file name
					res = lstr ;
					break ;									          // File found, return name
				}
				i++ ;
			}
			file = root.openNextFile() ;
	   }
	}
	return res ;
}


//***********************************************************************************************
//									                S H O W _ S D _ D I R										                    *
//***********************************************************************************************
// Show files on SD card.																		                                    *
// Print files like:																			                                      *
// If extension is "*", files with all extensions are listed.								                  	*
// ps8-focal71-teco-omsi.tu56																	                                  *
// os8v3d2-2.tu56																				                                        *
//***********************************************************************************************
void show_sd_dir ( const char* ext )
{
	uint16_t	fseq = 0 ;								            // Sequence number in directory
	char*		  p ;										                // Points to filename
	uint16_t  row, col ;            								// Cursor position

	while ( ( p = search_sd_dir ( ext, fseq ) ) )		// Search for this sequence
	{
		row = ( fseq % 15 ) + 16 ;						        // Row for text
		col = ( fseq / 15 ) * 40 ;						        // Column for text
		str_put ( "\e[%d;%df"							            // Got cursor position
				  "%s\e[K\r\n", row, col, p ) ;			      // Show filename, clear to EOL
		fseq++ ;										                  // Search next filename
	}
}


//***********************************************************************************************
//									                  G E T _ D E V N A M E										                  *
//***********************************************************************************************
// Get device name from devices table.  Special handling of RKAx/RKBx disks.					          *
//***********************************************************************************************
const char* get_devname ( uint16_t inx )
{
	static char devname[12] ;							            // Space for selected device name

	if ( strstr ( devicesx[inx].devname, "RKA" ) )
	{
		sprintf ( devname, "%s/%s",						          // Exception for RKAx/RKBx
				  devicesx[inx].devname,
				  devicesx[inx+1].devname ) ;
	}
	else
	{
		sprintf ( devname, "%s",						            // Normal hanling (not RXAx/RKBx
				  devicesx[inx].devname ) ;
	}
	return devname ;
}


//***********************************************************************************************
//									                  S H O W _ D E V S											                    *
//***********************************************************************************************
// Show devices available for LD/SV from/to SD card.											                      *
// Prints  like:																				                                        *
// Option SL 0 -> RKA0/RKB0																		                                  *
// Option SL 2 -> DTA0																			                                    *
//***********************************************************************************************
void show_devs()
{
	const char* p ;										              // Points to device name

	for ( int i = 0 ; i < NUMDEV ; i++ )				    // Show all devices
	{
		p = get_devname ( i ) ;							          // Get device name
		str_put ( "Option SL %d -> %s\r\n",				    // Format and show the option
				  i, p ) ;
		if ( strstr ( p, "RKA" ) )						        // Special RKAx/RKBx ?
		{
			i++ ;										                    // Skip RKBx
		}
	}
}


//***********************************************************************************************
//											                D U M P												                          *
//***********************************************************************************************
// Dump one page of words.																		                                  *
//***********************************************************************************************
void dump ( uint16_t df, uint16_t ma  )
{
	uint16_t  j, k ;									        // Loop control
	uint16_t  a ;										          // Temporary

	ma = ma & 07777 ;									        // Prevent crash
	df = df & 07 ;
	for ( j = 0 ; j < 128 ; j += 16 )					// Print one page, 16 words per line
	{
		a = ( ma + j ) & 07777 ;						    // Prevent overflow
		str_put ( "%o:%04o", df, a ) ;					// Print field and memory address
		for ( k = 0 ; k < 16 ; k++ )
		{
			if ( k == 8 )
			{
				str_put ( " " ) ;						        // Extra space after 8 locations
			}
			a = ( ma + j + k ) & 07777 ;				  // Prevent overflow
			str_put ( " %04o", MEM[df][a] ) ;			// Send to telnet client
		}
		str_put ( "\r\n" ) ;
	}
}


//***************************************************************************************************
//										                    S A V E _ S D												                      *
//***************************************************************************************************
// Save an image to SD card.  The filename must be supplied as the 2nd parameter.					          *
// The filename extension is forced to be ".rk05" / ".tu56" / ".rx01".								              *
// For RKA0/RKB0, the 2 devices are handle as one (RK05) disk.										                  *
//***************************************************************************************************
bool save_sd ( uint16_t sel, const char* nam )
{
	bool		    res = false ;														// Result, assume not okay
	char*	      ext ;										    						// Forced filename extension
	FILE*		    f ;											    						// File handle
	uint16_t	  dev ;										    						// For loop 2 devices
	uint16_t	  ndev = 1 ;															// Number of devices to copy
	uint16_t	  blk ;										    						// Block number to read
	uint16_t	  size ;										  						// Size of device in blocks
	bool		    istape ;									  						// True for DECtape device
	uint16_t	  n ;											    						// Number of elements written to SD
	wl_handle_t	hndl ;										  						// Handle for input device
	char		    fspec[100] ;														// File spec
	uint16_t	  dumwrd = 0 ;														// 129th word DECtape block

	if ( nam == NULL )										              // Filename supplied?
	{
		str_put ( "No filename!" ) ;				              // No, error return
		return res ;
	}
	if ( sel == 0 )											                // RKA0/RKB0 couple?
	{
		ndev = 2 ;											                  // Yes, copy 2 devices
	}
	ext = devicesx[sel].extension ;							        // Get extension
	size = devicesx[sel].size ;								          // Get size of device
	istape = devicesx[sel].istape ;							        // Check for DECtape
	if ( strstr ( nam, ext ) )								          // Extension supplied?
	{
		sprintf ( fspec, "/%s", nam ) ; 					        // Yes, form filespec
	}
	else
	{
		sprintf ( fspec, "/%s%s", nam, ext ) ;				    // Add missing extension
	}
	str_put ( "Writing %s image to SD file %s\r\n",			// Show activity
			  get_devname ( sel ), fspec ) ;
	f = fopen ( fspec, "w" ) ;								          // Open file for write
	if ( f == NULL )
	{
		str_put ( "File I/O error!\r\n" ) ;					      // Error opening file
		return res ;
	}
	for ( dev = 0 ; dev < ndev ; dev++ )					      // 1 or 2 input devices to do
	{
		hndl= devicesx[sel+dev].handle ;					        // Get handle
		str_put ( "\r\nCopying %s ",						          // Show activity
				  devicesx[sel + dev].devname ) ;
		for ( blk = 0 ; blk < size ; blk++ )				      // Loop for all blocks from device
		{
			if ( ( blk % 100 ) == 0 )						            // Show activity?
			{
				str_put ( "." ) ;
			}
			dskread ( hndl, wrdbuf, blk, 2 ) ;				      // Read one block
			if ( istape )									                  // Is it DECtape
			{
				n = fwrite ( wrdbuf, sizeof(uint16_t),		    // Write 128 words into DECtape block
							 128, f ) +
					fwrite ( &dumwrd, sizeof(uint16_t),		      // Write a dummy 129th word
							 1, f ) +
				    fwrite ( wrdbuf + 128, sizeof(uint16_t),  // Write 128 words of 2nd DECtape block
							 128, f ) +
				    fwrite ( &dumwrd, sizeof(uint16_t),		    // Write a dummy 129th word
							 1, f ) - 2 ;					                  // Correction for 2 dummy words

			}
			else
			{
				n = fwrite ( wrdbuf, sizeof(uint16_t),
							  256, f ) ;					                  // Write one block
			}
			if ( n < 256 )									                // Check result
			{
				str_put ( "\r\nFile write error side %d, "	  // Bad result
						  "block %d, n is %d\r\b",
						  dev, blk, n ) ;
				goto END ;									                  // Stop copy
			}
		}
	}
	str_put ( "\r\nCopy completed\n\r" ) ;					    // Show success
END:
	fclose ( f ) ;											                // Ready with this file
	return res ;
}


//***********************************************************************************************
//										                  L O A D _ S D											                      *
//***********************************************************************************************
// Load an image from SD card.																	                                *
// DECtapes have blocks of 129 words, the 129th word is not used in OS/8, so we skip that.		    *
//***********************************************************************************************
bool load_sd ( uint16_t sel, const char* filename )
{
	bool		    res = false ;								        // Assume negative result
	char*		    ext ;										            // Extension of filename
	uint16_t	  size ;										          // Size of device in blocks
	FILE*		    f ;											            // File handle
	static char	fspec[100] ;								        // Full filespec
	uint16_t	  length = 0 ;								        // Length of the file in blocks
	int			    n ;											            // Result fread
	uint16_t	  bcnt;										            // Block number on disk/tape partition
	uint32_t	  lofs ;										          // Offset in in file (bytes)
	bool		    istape ;									          // True if input from DECtape image
	uint16_t	  dumwrd ;									          // Dummy input from tape image

	lofs = devicesx[sel].offset * 512 ;						  // Offset if 2nd half of RK05
	ext = devicesx[sel].extension ;							    // Get filename extension
	size = devicesx[sel].size ;								      // Get size of device in blocks
	istape = devicesx[sel].istape ;							    // Read from tape image?
	if ( filename == NULL )									        // Check filename
	{
		str_put ( "No file specified!\r\n" ) ;				// Error opening file
		return res  ;										              // Does not exist
	}
	if ( strstr ( filename, ext ) == NULL )					// Check extension
	{
		sprintf ( fspec, "/%s%s\r\n",
				  filename, ext ) ;							          // Form full filespec, with extaension added
	}
	else
	{
		sprintf ( fspec, "/%s\r\n", filename ) ;			// Form full filespec
	}
	str_put ( "Open %s", fspec ) ;							    // Show to user
	f = fopen ( fspec, "rb" ) ;								      // Open file for read
	if ( f == NULL )
	{
		str_put ( "File I/O error!\r\n" ) ;					  // Error opening file
		return res ;
	}
	if ( fseek ( f, 0, SEEK_END ) == 0 )					  // Got to end of requested data
	{
		if ( istape )										              // For tape different blocksize
		{
			length = ftell ( f ) / 516 ;					      // Get total length in blocks
		}
		else
		{
			length = ftell ( f ) / 512 ;					      // Get total length in blocks
		}
	}
	if ( fseek ( f, lofs, SEEK_SET ) != 0 )					// Go to begin of requested data
	{
		str_put ( "SEEK_SET error!\r\n" ) ;					  // Report SEEK error
		goto END ;										              	// and quit
	}
	if ( length < size )									          // Length must be at least the size
	{
		str_put ( "File size error, %d < %d!",				// Length less than expected image size
				  length, size ) ;
		goto END ;											              // Quit
	}
	str_put ( "Copying %d blocks from SD to %s. "
			  "This may take about %d seconds...\r\n",
			  size, devicesx[sel].devname, size / 60 ) ;
	for ( bcnt = 0 ; bcnt < size ; bcnt++ )					// Copy whole file or half of file
	{
		//dbgprint ( "Read %d bytes", 512 ) ;
		if ( istape )
		{
			n = fread ( wrdbuf,
						sizeof(uint16_t), 128, f ) +		      // Read 128 words from dectape block
				fread ( &dumwrd,
						sizeof(uint16_t), 1,   f ) +		      // Read unused word
				fread ( wrdbuf + 128,
						sizeof(uint16_t), 128, f ) +		      // Read 128 words from dectape block
				fread ( &dumwrd,
						sizeof(uint16_t), 1,   f ) - 2 ;	    // Read unused word, compensate for dummies
		}
		else
		{
			n = fread ( wrdbuf, sizeof(uint16_t),       // Read one block
                  256, f) ;	
		}
		if ( n != 256 )
		{
			str_put ( "\r\nfread error, n is %d!", n ) ;
			goto END ;
		}
		if ( !dskwrite ( devicesx[sel].handle,			  // Write 2 pages to disk
                     wrdbuf, bcnt, 2 ) )
		{
			str_put ( "\r\nESP32 flash write error!" ) ;
			goto END ;										              // Error, end download
		}
		if ( ( bcnt % 100 ) == 0 )							      // Show activity?
		{
			str_put ( "." ) ;
		}
	}
	res = true ;											              // Result is okay
	flushcache() ;											            // Force actual write
	str_put ( "\r\nCopy completed\n\r" ) ;					// Show success
END:
	fclose ( f ) ;
	return res ;
}


//***********************************************************************************************
//											                  C L P												                          *
//***********************************************************************************************
// Clear lower part of screen.																	                                *
//***********************************************************************************************
void clp()
{
	str_put ( "\e[17;0f\e[J" ) ;					  // Cursur to dump position, clear to EOS
}


//***********************************************************************************************
//											                  T C M D												                        *
//***********************************************************************************************
// Compare a command with a string.  Command may be upper/lower case.							              *
// Pattern must be upper case.																	                                *
//***********************************************************************************************
bool tcmd ( const char* command, const char* pattern )
{
	bool		  res = true ;								  // Assume equal
	int			  c ;											      // Uppercased char in command
	uint16_t	i ; 										      // Loop control

	for ( i = 0 ; pattern[i] ; i++ )
	{
		c = command[i] ;									    // Get char from command
		c = toupper ( c ) ;									  // Convert to upper case
		res &= ( c == pattern[i] ) ;					// Compare
	}
	return res ;
}


//***********************************************************************************************
//									                  E X _ M N U _ C M D											                  *
//***********************************************************************************************
// Execute a menu command.																		                                  *
// Examples:																					                                          *
// CO				- Continue at current location.												                              *
// CO 200			- Continue at 0200 in the current IF.										                          *
// CO 1 2200		- Continue at 2200 in IF 1.													                            *
// ST				- Start at 7605 in IF/DF 0 (AC and link set to zero). Starts OS/8.			            *
// ST 1 2200		- Start at 2200 in IF/DF 1 (AC and link set to zero).						                *
// LD os8v3.rk05	- Load rk05 image (RKA0 and RKB0) from SD card.								                *
// DU 5 1000		- Dump a page from location 1000 in field 5.								                    *
// DU				- Dump next page.															                                      *
//***********************************************************************************************
void ex_mnu_cmd ( const char *cmd )
{
	unsigned int	ui ;									// For sscanf
	static uint16_t	dumpdf = 0 ;							// Default dump DF
	static uint16_t	dumpaddr = 0200 ;						// Default dump address
	const char*		p ;										// Points into cmd
	const char*		pa = NULL ;								// Alfanumerical parameter 1
	int16_t			p1 = -1 ;								// Numerical parameters 1 in command
	int16_t			p2 = -1 ;								// Numerical parameters 1 in command
	const char*		dvnam ;									// Points to device name in devices

	p = strstr ( cmd, " " ) ;  								// Parameter 1 supplied?
	if ( ( p != NULL && ( strlen(p) > 1 ) ) )				// Reasonable parameter?
	{
		pa = p + 1 ;										// Move beyond space
		if ( sscanf ( pa, "%o", &ui ) == 1 )				// Get p1
		{
			p1 = ui ;
			p = strstr ( p + 2, " " ) ;						// Parameter 2 supplied?
			if ( ( p != NULL && ( strlen(p) > 1 ) ) )		// Reasonable parameter?
			{
				if ( sscanf ( p, "%o", &ui ) == 1 )			// Get p2
				{
					p2 = ui ;
				}
			}
		}
	}
	clp() ;													// Clear lower part of screen
	if ( tcmd ( cmd, "CO" ) )								// Continue command?
	{
		running = true ;									// Restart interpreter
	}
	else if ( tcmd ( cmd, "DU" ) )							// Dump command?
	{
		if ( p2 >= 0 )
		{
			dumpdf = p1 ;									// New DF
			dumpaddr = p2 ;									// And address
		}
		else if ( p1 >= 0 )									// Address only specified?
		{
			dumpaddr = p1 ;									// New address
		}
		dump ( dumpdf, dumpaddr ) ;							// Dump 128 words
		dumpaddr = ( dumpaddr+0200 ) & 07777 ;				// Default next 128 words
	}
	else if ( tcmd ( cmd, "BO" )  )							// Boot command?
	{
		boot() ;											// Yes, GO.  Will set running to true
	}
	else if ( tcmd ( cmd, "ST" ) )							// Start at 7605 command
	{
		AC = 0 ;											// Clear AC and link
		if ( p2 >= 0 )										// 2 parameters?
		{
			IF = DF = p1 ;									// Yes, set IF and DF
			PC = p2 ;
		}
		else if ( p1 >= 0 )									// At least 1 parameter
		{
			PC = p1 ;										// Set PC
		}
		else
		{
			PC = 07605 ;									// Continue at 7605
			IFpending = IF = DF = 0 ;						// DF and IF to 0
		}
		running = true ;
	}
	else if ( tcmd ( cmd, "SL" ) )							// Select device for LD/SV?
	{
		if ( p1 >= 0 )
		{
			if ( p1 < NUMDEV )								      // Check parameter, user uses 0..5
			{
				seldev = p1 ;								          // Set new selected device
				menu_state = START ;						      // Show in refreshed menu
			}
			else
			{
				str_put ( "%0o is an illegal selection",
						  p1 ) ;
			}
		}
		else
		{
			show_devs() ;
		}
	}
	else if ( tcmd ( cmd, "DW" ) )							      // Download image?
	{
		if ( pa == NULL )									              // URL supplied?
		{
			//pa = "www.pdp8online.com"
			//	   "/ftp/images/os8/diag-games-kermit.rk05" ;
			pa = "www.smallenburg.nl"
				 "/pdp8/os8patched.rk05" ;
		}
		download ( pa ) ;									              // Download a fresh image
	}
	else if ( tcmd ( cmd, "LD" ) )							      // Load image from SD?
	{
		if ( pa )											                  // Parameter supplied?
		{
			if ( card_okay )
			{
				dvnam = devicesx[seldev].devname ;			    // Get device name
				load_sd ( seldev, pa ) ;					          // Load file from SD to selected device
				if ( strstr ( dvnam, "RKA" ) )				      // RKAx/RKBx ? 
				{											                      // Special handling for RKAx/RKBx
					load_sd ( seldev + 1, pa ) ;			        // 2nd half of image to RKBx
				}
			}
		}
		else
		{
			show_sd_dir ( devicesx[seldev].extension ) ;	// 0 parameters, show files on card
		}
	}
	else if ( tcmd ( cmd, "UC" ) )							      // Toggle Upper/Lower case
	{
		uppercase = !uppercase ;
	}
	else if ( tcmd ( cmd, "SR" ) )							      // Set switch register
	{
		if ( p1 >= 0 )
		{
			SR= p1 ;
		}
    menu_status() ;                                 // Show new status
	}
	else if ( tcmd ( cmd, "PO" ) )							      // Power-off
	{
		str_put ( "Flush cache\r\n" ) ;						      // Show action
		str_put ( "Go to sleep\r\n" ) ;
		flushcache() ;										              // Force write of cached data
		if ( PTPhandle )									              // PTP output open?
		{
			fclose ( PTPhandle ) ;							          // Yes, close
			PTPhandle = NULL ;								            // And clear handle
		}
		abortf = true ;										              // Abort system
	}
	else if ( tcmd ( cmd, "FL" ) )
	{
		flushcache() ;										              // Force write of cached data
		if ( PTPhandle )									              // PTP output open?
		{
			fclose ( PTPhandle ) ;							          // Yes, close
			PTPhandle = NULL ;								            // And clear handle
		}
	}
	else if ( tcmd ( cmd, "SV" ) )							      // Save image to SD
	{
		save_sd ( seldev, pa ) ;
	}
	else if ( tcmd ( cmd, "PR" ) )							      // Specify input for simulated PTR?
	{
		if ( pa )
		{
		  sprintf ( PTRfile, "/%s", pa ) ;					    // Yes, set filename
		  menu_state = START ;								          // To show the new filename
		}
		else
		{
			show_sd_dir ( "*" ) ;							            // 0 parameters, show files on card
		}
	}
	else if ( tcmd ( cmd, "PP" ) )							      // Specify output for simulated PTP?
	{
		if ( pa )
		{
		  sprintf ( PTPfile, "/%s", pa ) ;					    // Yes, set filename
		  menu_state = START ;								          // To show the new filename
		}
	}
	else if ( tcmd ( cmd, "XX" ) )							      // TEST: Load block from selected device
	{														                      // into 00200
		if ( p1 >= 0 )										              // There should be a parameter
		{
			str_put ( "Read %s: block %o\r\n",
					  devicesx[seldev].devname, p1 ) ;
			dskread ( devicesx[seldev].handle,
					  &MEM[0][0200], p1, 2 ) ;
			dumpdf = 0 ;									                // New DF
			dumpaddr = 0200 ;								              // And address
			dump ( dumpdf, dumpaddr ) ;						        // Dump 128 words
			dumpaddr = 0400 ;								              // Next page
			dump ( dumpdf, dumpaddr ) ;						        // Dump 128 words
		}
	}
	else
	{
		// Unknown command
	}
	if ( menu_state == WAIT_CMD )							        // Still in command mode?
	{
		str_put ( "\e[u\e[K" ) ;							          // Unsave cursor and clear command
	}
	if ( running )											              // Ready with menu?
	{
		str_put ( "\e[2J\e[H" ) ;							          // Yes, erase screen, home
		menu_state = START ;								            // Set to "start" for next menu
	}
}


//***********************************************************************************************
//										              M E N U _ S T A T U S 								                      *
//***********************************************************************************************
// Show PDP8 status.                                                                            *
//***********************************************************************************************
void menu_status()
{
  str_put ( "\e[s" ) ;								          // Save cursor
  str_put ( "\e[16;0f" ) ;							        // Cursor to status position
  str_put ( "\e[32m") ;								          // Green
  str_put ( "PC %o:%04o  -  DF %o  -  "				  // Show machine status
        "AC %o:%04o  -  MQ %04o  -  "
        "MB %04o  -  SR %04o",
        IF, PC - 1, DF, AC >> 12, AC & 07777,
        MQ, MEM[IF][PC-1], SR ) ;
  str_put ( "\e[37m") ;								          // White
  str_put ( "\e[u" ) ;								          // Unsave cursor
}


//***********************************************************************************************
//										                    M E N U													                      *
//***********************************************************************************************
// Handle the menu.																				                                      *
//***********************************************************************************************
void menu()
{
	static const char*     menutxt =
			"\e[2J\e[H"										              // Erase screen, cursor home
			"\e[1m"											                // Bright intensity
			"Control console for PDP8 emulator.\r\n"
			"\e[0m"											                // Normal intensity
			"Entered on cpu HLT or Ctrl-A key.\r\n"
			"Enter one of the following options:"
			"\e[5;0f"   "CO - Continue"
			"\e[6;0f"   "DU - Dump one page"
			"\e[7;0f"   "BO - Boot from RKA0:"
			"\e[8;0f"   "ST - Start OS/8 at 0:7605"
			"\e[9;0f"   "UC - Toggle UPPER case flag"
			"\e[10;0f"  "SR - Set switch register"
			"\e[11;0f"  "PR - Set filename for PTR"
			"\e[5;40f"  "PO - Power-off"
			"\e[6;40f"  "DW - Download RKA0+RKB0 image"
			"\e[7;40f"  "SL - Select device for LD/SV"
			"\e[8;40f"  "LD - Load image from SD card"
			"\e[9;40f"  "SV - Save image to SD card"
			"\e[10;40f" "FL - Flush cache buffers"
			"\e[11;40f" "PP - Set filename for PTP"
			"\e[14;0f"
			"Option: " ;
	uint8_t			    c ;										          // Input character
	static char		  cmd[130] ;								      // Input from user
	static uint16_t	inx ;									          // Index in command
  
  if ( menu_state == IDLE )                       // Quick return if idle
  {
    return ;
  }
	if ( menu_state == WAIT_ANY )							      // Waiting for any key?
	{
		if ( kbd_available() )								        // Any input?
		{
			kbd_get() ;										              // Yes, read char and discard
			menu_state = START ;							          // State is now START
		}
	}
	if ( menu_state == START )								      // Have to display the menu?
	{
		str_put ( menutxt ) ;								          // Send to telnet client
    menu_status() ;                               // Shpw status
		str_put ( "\e[33m") ;								          // Yellow
		str_put ( "\e[1;42f"								          // Position for current LD/SV device
		          "Current LD/SV device is %s",
				   get_devname ( seldev ) ) ;
		str_put ( "\e[2;42f"								          // Position for current PTR file
		          "Current PTR file is %s", PTRfile ) ;
		str_put ( "\e[3;42f"								          // Position for current PTR file
		          "Current PTP file is %s", PTPfile ) ;
		str_put ( "\e[37m") ;								          // White
		str_put ( "\e[u" ) ;								          // Unsave cursor
		menu_state = WAIT_CMD ;								        // Start waiting for command
		inx = 0 ;											                // Put characters at the beginning
	}
	if ( menu_state == WAIT_CMD )							      // Waiting for user input?
	{
		if ( kbd_available() )								        // Any input?
		{
			c = kbd_get() ;									            // Yes, read char
			if ( inx < 2 )									            // Command character?
			{
				c = toupper ( c ) ;							          // Make upper case
			}
			c_put ( c ) ;									              // Echo
			if ( c == '\r' )								            // CR typed?
			{
				cmd[inx] = '\0' ;							            // Delimit command
				inx = 0 ;									                // Ready for new command
				ex_mnu_cmd ( cmd ) ;						          // And execute it
			}
			else if ( c == 0x7F )							          // RUBOUT?
			{
				if ( inx )									              // Part of command left?
				{
					//str_put ( "\b \b" ) ;					        // Remove last char from screen
					inx-- ;									                // Adjust index
				}
				else
				{
					menu_state = START ;					          // No, start all over
				}
			}
			else if ( c == ( 'A' & 0x3F ) )		          // Control-A?
			{
				menu_state = START ;						          // Yes, start all over
			}
			else
			{
				// CR will sometimes be followed by a NULL character
				if ( c >= 040 )								            // Skip control characters
				{
					cmd[inx++] = c ;						            // Store in command buffer
				}
				if ( inx >= sizeof(cmd) )					        // Prevent overflow
				{
					menu_state = START ;					          // Start all over
				}
			}
		}
	}
}


//***********************************************************************************************
//									                    W E L C O M E												                    *
//***********************************************************************************************
// Sends a welcoming message to the telnet client.												                      *
//***********************************************************************************************
void welcome()
{
	const char*	 msg =	"\e[2J\e[H"										              // Erase screen, cursor home
						          "Welcome to PDP8 simulator running OS/8\r\n"
						          "Written by Ed Smallenburg\r\n\n" ;
	char	       buf ;
	int16_t      n = 0 ;

	menu_state = IDLE ;										                  // Disable menu
	while ( n > 0 )
	{
		vTaskDelay ( 10 / portTICK_PERIOD_MS ) ;
		n = clientRecv ( &buf, 1 ) ;              		        // Skip all garbage input
	}
	str_put ( msg ) ;											                  // Sent to telnet client
	if ( card_okay )											                  // SD card found?
	{
		str_put ( "SD card found on this system.\r\n\n" ) ;		// Yes, show!
	}
	str_put ( "\nPress any key to continue... " ) ;
	menu_state = WAIT_ANY ;										              // Wait for a key
}


//***********************************************************************************************
//								                T E L N E T T A S K    			                      						*
//***********************************************************************************************
// Create a listening socket.  Then we wait for a client to connect.							              *
// Once a client has connected, we then read until there is no more data.						            *
// We then close the client socket and start waiting for a new connection.						          *
//***********************************************************************************************
void telnetTask ( void *pvParameter )
{
	struct sockaddr_in	clientAddress ;
	struct sockaddr_in	serverAddress ;
	socklen_t			      clientAddressLength ;
	int					        sock ;							  	            // Socket for listen
	int					        rc ;								                // Result of bind/listen

	sock = socket ( AF_INET, SOCK_STREAM, IPPROTO_TCP ) ;		// Create socket for listen
	if ( sock < 0 )												                  // Check result
	{
		dbgprint ( "%s", strerror ( errno ) ) ;					      // Report problem
		goto END ;
	}
	serverAddress.sin_family      = AF_INET ;					      // Bind our server socket to a port.
	serverAddress.sin_addr.s_addr = htonl ( INADDR_ANY ) ;
	serverAddress.sin_port        = htons ( TELNET_PORT ) ;	// Listen on this port
	rc  = bind ( sock, (struct sockaddr *)&serverAddress,		// Bind
			         sizeof(serverAddress) ) ;
	if ( rc < 0 )												                    // Check result
	{
		dbgprint ( "bind: %d %s",								              // Report error
				rc, strerror ( errno ) ) ;
		goto END ;
	}
	// Flag the socket as listening for new connections.
	rc = listen ( sock, 1 ) ;									              // Listen for 1 connection
	if ( rc < 0 )												                    // Check for error
	{
		dbgprint ( "listen: %d %s", 							            // Report error
				rc, strerror(errno) ) ;
		goto END ;
	}
	dbgprint ( "Telnet is listening.." ) ;
	while ( !abortf )											                  // Listen for a new client connection.
	{
		lc_telnet++ ;											                    // Count number of loops
		clientAddressLength = sizeof(clientAddress) ;
		clientSock = accept ( sock,
				  (struct sockaddr *)&clientAddress,
				  &clientAddressLength ) ;
		if ( clientSock < 0 )									                // Check for error
		{
			dbgprint ( "accept: %d %s",							            // Report error
					       clientSock, strerror(errno) ) ;
			goto END;
		}
		dbgprint ( "New client connected" ) ;					        // We now have a new client ...
		welcome() ;												                    // Display welcome message
		while ( clientSock >= 0 )
		{
      vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;           // Just pause
    }
	}
	END:
	if ( clientSock >= 0 )										              // Socket active?
	{
		close ( clientSock ) ;									              // Yes, close it
    clientSock = -1 ;
	}
	vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;					      // Give some time
	vTaskDelete ( NULL ) ;									                // End of task
}


//***********************************************************************************************
//								                    U S E R T A S K    			                      						*
//***********************************************************************************************
// Handle user commands for the menu and user input/output for TTY.  							              *
// Input from TelNet or serial port.                                                            *
//***********************************************************************************************
void userTask ( void *pvParameter )
{
	char				        c ;									               	// Char buffer for in/output
	int					        n ;										              // Nr of chars read from socket
	bool				        idle ;									            // True if no activity
  static bool         once = true ;                       // Welcome text just once

  vTaskDelay ( 1000 / portTICK_PERIOD_MS ) ;				      // Give some time before start
	while ( !abortf )  											                // Listen for a command
	{
		lc_user++ ;											                      // Count number of loops
    idle = true ;										                      // Assume no activity
    if ( uxQueueSpacesAvailable ( kbd_queue ) )			      // Do we have space for keystrokes?
    {
      n = clientRecv ( &c, 1 ) ;						              // Read 1 character from client, no blocking
      if ( n > 0 )									                      // Any input?
      {
        idle = false ;								                    // Activity detected
        if ( c == ( 'A' & 0x3F ) )  				              // Ctrl-A ?
        {
          running = false ;						                    // Stop PDP8
          if ( once )                                     // Yes, welcome text?
          {
         		welcome() ;											              // Yes, display welcome message
            once = false ;
          }
          else
          {
            menu_state = START ;				                  // Force start of menu
          }
          if ( clientSock < 0 )                           // Input from serial?
          {
            DEBUG = false ;   	                          // Yes, stop debug output
          }
          dbgprint ( "Ctrl-A seen" ) ;
        }
        else if ( c )								                      // Skip NULL character
        {
          xQueueSend ( kbd_queue, &c, 0 ) ;		            // Send to keyboard queue
        }
      }
    }
    else
    {
      dbgprint ( "Keyboard queue full" ) ;
    }
    if ( uxQueueMessagesWaiting ( tls_queue ) )			      // Something to send?
    {
      xQueueReceive ( tls_queue, &c, 0 ) ;			          // Yes, get next char
      clientSend ( &c, 1 ) ;                    		      // Sent to user
      idle = false ;									                    // State is not idle
    }
    if ( idle )											                      // Nothing to do, wait some time
    {
      vTaskDelay ( 10 / portTICK_PERIOD_MS ) ;		        // Sleep some time
    }
    if ( !running )
    {
      menu() ;										                        // Handle menu
    }
  }
	vTaskDelay ( 1000 / portTICK_PERIOD_MS ) ;				      // Give some time at power off
	vQueueDelete ( kbd_queue ) ;								            // Clean-up the queues
	vQueueDelete ( tls_queue ) ;
	#ifdef OLEDDISPLAY
		vTaskDelete ( th_console ) ;							            // End of display task (if any)
	#endif
	dbgprint ( "Stopping CPU, go to sleep" ) ;
	#ifdef OLEDDISPLAY
		display->clear() ;										                // Clear the display
    #endif
	vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;					      // Give some time to clear
	//esp_deep_sleep_start() ;									            // and go to sleep
	// Will not return here...
	//vTaskDelete ( NULL ) ;									              // End of task
}


#ifdef OLEDDISPLAY
//***********************************************************************************************
//								                C O N S O L E T A S K  											                  *
//***********************************************************************************************
// Task to simulate the console ligths on the OLED.												                      *
//***********************************************************************************************
void consoleTask ( void *pvParameter )
{
	bool once = true ;												        // Start with complete refresh

	dbgprint ( "console task started" ) ;
  display = new OLED ( "SSD" ) ;									  // Create SSD1306 instance
	display->clear() ;												        // Clear and init screen
  while ( true )
	{
		vTaskDelay ( 20 / portTICK_PERIOD_MS ) ;				// Sleep for 20 milliseconds
		if ( once )												              // Draw markers?
		{															                  // Yes
			display->setmarkers ( 0, 0777777 ) ;					// Markers for DF, IF and PC
			display->setmarkers ( 1,   07777 ) ;					// Markers for MA
			display->setmarkers ( 2,   07777 ) ;					// Markers for MB
			display->setmarkers ( 3,  017777 ) ;					// Markers for L and AC
			display->setmarkers ( 4,   07777 ) ;					// Markers for MQ
		}
		display->show_register ( 0, 0777777, 						// DF, IF and PC
	                           DF << 15 | IF << 12 | PC ) ;
		display->show_register ( 1,   07777, MA ) ;			// MA
		display->show_register ( 2,   07777, MB ) ;			// MB
		display->show_register ( 3,  017777, AC ) ;			// L and AC
		display->show_register ( 4,   07777, MQ ) ;			// MQ
		display->display ( once ) ;		    						  // Show it
		once = false ;												          // Limit refresh after first run
	}
}
#endif

//***********************************************************************************************
//									            I N I T I A L I Z E _ W I F I								                    *
//***********************************************************************************************
// Init Wifi connection.																		                                    *
//***********************************************************************************************
static void initialize_wifi ( void )
{
	int8_t    count = 5 ;
	IPAddress ip ;

	WiFi.disconnect ( true ) ;								                // After restart the router could
	WiFi.softAPdisconnect ( true ) ;						              // still keep the old connection
	vTaskDelay ( 1000 / portTICK_PERIOD_MS ) ;				        // Silly things to start connection
	WiFi.mode ( WIFI_STA ) ;
	WiFi.begin ( WIFI_SSID, WIFI_PASSWORD ) ;
	while ( ( WiFi.status() != WL_CONNECTED ) && ( count > 0) )
	{
		delay ( 2000 ) ;
		dbgprint ( "Connecting to WiFi %s..", WIFI_SSID ) ;
		if ( ( --count % 2 ) == 0 )
		{
			dbgprint ( "Reconnect" ) ;
			WiFi.reconnect() ;
		}
	}
	if ( count == 0 )
	{
		dbgprint ( "WiFi connection failed!" ) ;
        dbgprint ( "Trying to setup AP "
                   "with name %s and password %s.",
                   NAME, NAME ) ;
        WiFi.mode ( WIFI_AP ) ;                             // ESP32 wordt een access point
        vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;           // 100 ms delay
        WiFi.softAP ( NAME, NAME ) ;                        // This ESP will be an AP
		ip = IPAddress ( 192, 168, 4, 1 ) ;					            // Set AP mode IP address
	}
	else
	{
		apmode = false ;
		ip = WiFi.localIP() ;								                    // Get IP address
	}
    dbgprint ( "Connected to WiFi, IP is %s",				        // Show IP
	           ip.toString().c_str() ) ;
}


//***********************************************************************************************
//								                I N I T I A L I Z E _ S N T P									                *
//***********************************************************************************************
// Init sntp to get current time.																                                *
//***********************************************************************************************
static void initialize_sntp ( void )
{
	dbgprint ( "Initializing SNTP" ) ;
	sntp_setoperatingmode ( SNTP_OPMODE_POLL ) ;
	sntp_setservername ( 0, "pool.ntp.org" ) ;
	sntp_init() ;
}


//***********************************************************************************************
//										                O B T A I N _ T I M E									                    *
//***********************************************************************************************
// Get current time.																			                                      *
//***********************************************************************************************
static void obtain_time ( void )
{
	time_t    now = 0 ;
	int       retry = 0 ;
	const int retry_count = 10 ;
	uint16_t  yearbits ;								                    // 5 year-bits for OS/8

	initialize_sntp() ;									                    // wait for time to be set
	while ( timeinfo.tm_year < (2016 - 1900) &&
          ++retry < retry_count)
	{
		if ( apmode )									                        // No internet if in AP mode
		{
			break ;
		}
		dbgprint ( "Waiting for system time to be set... (%d/%d)", retry, retry_count ) ;
		vTaskDelay ( 4000 / portTICK_PERIOD_MS ) ;
		time ( &now ) ;
		//setenv ( "TZ",  "CET-1CEST-2,M3.5.0/02:00:00,M10.5.0/03:00:00" ) ;     // Time zone Europe/Amsterdam
		//setenv ( "TZ",  "NZST-12NZDT-13,M10.1.0/02:00:00,M3.3.0/03:00:00" ) ;  // Timezone for New Zealand
		setenv ( "TZ", TIMEZONE, true ) ;				              // See config.h
		tzset() ;
		localtime_r ( &now, &timeinfo ) ;
	}
	if ( timeinfo.tm_year < ( 2016 - 1900 ) )
	{
		timeinfo.tm_year = 2023 - 1900 ;					            // Use default date
		timeinfo.tm_mon  = 6 - 1 ;							              // 01-JUN-2023
		timeinfo.tm_mday = 1 ;
    	timeinfo.tm_hour = 12 ;                             // !2:00:00
		timeinfo.tm_min = 0 ;
		timeinfo.tm_sec = 0 ;
		dbgprint ( "System time NOT set, "
				   "default used." ) ;
	}
	dbgprint ( "Time is set to "
			"%02d-%02d-%04d - %02d:%02d:%02d",				          // Yes, format to a string
			timeinfo.tm_mday,
			timeinfo.tm_mon + 1,
			timeinfo.tm_year + 1900,
			timeinfo.tm_hour,
			timeinfo.tm_min,
			timeinfo.tm_sec ) ;
	yearbits = timeinfo.tm_year % 100 ;						          // Last 2 digits of year
	os8date = ( ( timeinfo.tm_mon + 1 ) << 8 ) |			      // Form OS/8 date
			  ( timeinfo.tm_mday << 3 ) |
			  ( yearbits & 07 ) ;					 		                  // Valid from 2000 to 2037
	os8datex = ( yearbits & 030 ) << 4 ;					          // Extended year bits
}


//***********************************************************************************************
//										                    D V M O U N T                   											*
//***********************************************************************************************
// Mount the devices.  The devices are in fact partitions in flash.								              *
// Handle will be set to invalid if partition does not exists.									                *
//***********************************************************************************************
void dvmount ( wl_handle_t* handle, const char* partname, uint16_t minsize )
{
	esp_partition_iterator_t	pi ;						              // Iterator for find
	const esp_partition_t*		p ;							              // Pointer to partition struct
	esp_err_t					result = ESP_OK ;
	uint16_t					actsize ;					                    // Actual partition size in OS/8 blocks

	pi = esp_partition_find ( ESP_PARTITION_TYPE_DATA,		  // Get partition iterator for
			ESP_PARTITION_SUBTYPE_ANY,						              // this partition
			partname ) ;
	if ( pi == NULL)
	{
		dbgprint ( "- - %4s not available on 4MB "			      // Partition does not exist
		           "flash version", partname ) ;
		*handle = WL_INVALID_HANDLE ;						              // Set handle to invalid
		result = ESP_FAIL ;
	}
	else
	{
		p = esp_partition_get ( pi ) ;						            // Get partition struct
		esp_partition_iterator_release ( pi ) ;				        // Release the iterator
		result = wl_mount ( p, handle ) ;
		if ( result != ESP_OK )
		{
			dbgprint ( "Failed to mount wear leveling layer. Result = %d", result ) ;
		}
	}
	if ( result == ESP_OK )
	{
		actsize = wl_size ( *handle ) / 4096 * PPS / 2 ;	    // Actual size
		if ( actsize < minsize )
		{
			dbgprint ( "Partion %4s is too small!",
					   partname ) ;
			result = ESP_FAIL ;
		}
		dbgprint ( "%d - %4s mounted, "
				"size %06X bytes (%4d OS/8 blocks) "
				"%4d blocks used",
				*handle,
				partname,
				wl_size ( *handle ),
				actsize,
				minsize) ;
	}
}


//***********************************************************************************************
//										                  W R I T E S E C											                    *
//***********************************************************************************************
// Store a dirty buffer to flash.																                                *
// If free is true: set the cached sector to free (handle will be cleared.						          *
//***********************************************************************************************
bool writesec ( uint16_t inx, bool ffree )
{
	esp_err_t		    result ;							            // Result of partition access
	uint16_t		    w0, w1, w2 ;						          // 4th word buffer
	uint16_t*		    pout ;								            // Pointer for packed buffer
	const uint16_t*	pin ;								              // Points to PDP8 words in buffer
	uint16_t		    i ;									              // Loop control

	if ( dcache[inx]->dirty )							            // Write necessary?
	{
		pout = sectorbuf ;								              // Point to begin of packed sector buffer
		pin = dcache[inx]->cbuf ;						            // Points to PDP8 words
		for ( i = 0 ; i < ( PPS * 128 ) ; i += 4 )		  // 128 words per page
		{
			w0 = *pin++ & 07777 ;						              // Copy 3 words
			w1 = *pin++ & 07777 ;
			w2 = *pin++ & 07777 ;
			*pout++ = w0 | ( ( *pin & 00017 ) << 12 ) ;   // Bits 8-11 of 4th word to w0
			*pout++ = w1 | ( ( *pin & 00360 ) << 8 ) ;    // Bits 4-7 of 4th word to w1
			*pout++ = w2 | ( ( *pin & 07400 ) << 4 ) ;    // Bits 0-3 of 4th word to w2
			pin++ ;										                    // Pointer to next group of 4 words
		}
		result = wl_erase_range ( dcache[inx]->handle,  // Erase the part that must be written
				dcache[inx]->soffset,
				sizeof(sectorbuf) ) ;
		if ( result != ESP_OK )
		{
			dbgprint ( "wl_erase_range failed,"
					" result = %d",						                // Log the error
					result ) ;
			return false ;
		}
		//dbgprint ( "Actual write to offset %06X, data %06o %06o %06o %06o",
		//		dcache[inx]->soffset, sectorbuf[0], sectorbuf[1], sectorbuf[2], sectorbuf[3] ) ;
		result = wl_write ( dcache[inx]->handle,		    // Write the sector
				dcache[inx]->soffset,
				sectorbuf,
				sizeof(sectorbuf) ) ;
		//result = wl_read ( dcache[inx]->handle,
		//				   dcache[inx]->soffset,		          // Read back the sector
		//				   sectorbuf,
		//				   sizeof(sectorbuf) ) ;
		//dbgprint ( "Read back of offset    %X, data %06o %06o %06o %06o",
		//		dcache[inx]->soffset, sectorbuf[0], sectorbuf[1], sectorbuf[2], sectorbuf[3] ) ;
		if ( result != ESP_OK )							            // Check result
		{
			dbgprint ( "wl_write failed,"
					" offset = %X, result = %d",
					dcache[inx]->soffset, result ) ;
			return false ;
		}
		dcache[inx]->dirty = false ;					          // Not dirty anymore
		if ( ffree )									                  // Release cached sector?
		{
			dcache[inx]->handle = ILLHANDLE ;			        // Yes, set to unused
		}
	}
	return true ;
}


//***********************************************************************************************
//										                F L U S H C A C H E										                    *
//***********************************************************************************************
// Flush the dirty cachebuffers to the disk/tape image.											                    *
//***********************************************************************************************
void flushcache()
{
	uint16_t i ;										        // Loop control

	for ( i = 0 ; i < CACHESIZE ; i++ )
	{
		writesec ( i, false ) ;							  // Force actual write
	}
}


//***********************************************************************************************
//									                L O A D S E C T O R											                    *
//***********************************************************************************************
// Load the right sector in cache. The index in the cache will be returned to the caller.		    *
// If the sector is already in cache, the index will be returned without any I/O.				        *
// If the sector is not in cache, it will be loaded into a free cache slot.						          *
// If there is no free cache slot available, the least recently slot will be saved in flash (if	*
// "dirty") and the requested sector will be loaded into this freed slot.						            *
//***********************************************************************************************
int16_t loadsector ( wl_handle_t handle, uint32_t secoffset )
{
	uint16_t  i ;										        // Loop control
	uint16_t  freeinx ;									    // Index of free entry
	bool      freefound = false ;						// True if free slot found
	esp_err_t result ;									    // Result of partition access
	uint16_t* pin ;										      // Pointer for buffer with PDP8 words
	uint16_t* pout ;									      // Destination pointer in cache
	uint16_t  wbuf ;									      // 4th word formed from 3 x 4 bits
	uint32_t  minatime  = 0xFFFFFFFF ;			// To find least recently buffer
	uint16_t  oldstinx = 0 ;							  // Index of oldest buffer found

	for ( i = 0 ; i < CACHESIZE ; i++ )
	{
		if ( ( dcache[i]->handle == handle ) &&			  // Is this a cached sector for this handle?
				( dcache[i]->soffset == secoffset ) )	    // And is it the right one?
		{
			dcache[i]->atime = atime++ ;				        // Yes, found it
			//dbgprint ( "loadsector %X has cache %d",
			//		   secoffset, i ) ;
			return i ;									                // Return index
		}
		if ( !freefound )								              // Free cache buffer already found?
		{
			if ( dcache[i]->handle == ILLHANDLE )		    // No, is this a free cache buffer?
			{
				freefound = true ;						            // Yes, remember availability
				freeinx = i ;							                // Remember index
			}
			else if ( dcache[i]->atime < minatime )		  // Is this buffer older than previous?
			{
				minatime = dcache[i]->atime ;			        // Yes, remember oldest time and index
				oldstinx = i ;
			}
		}
	}
	if ( !freefound )									              // Sector is not cached, free sector?
	{
		// No free entry.  We have to release the least recently used sector in cache.
		//dbgprint ( "loadsector, no free buffer, write cache %d",
		//		      oldstinx ) ;
		writesec ( oldstinx, true ) ;					        // Write buffer to flash if dirty
		freeinx = oldstinx ;							            // Now we have a free buffer
	}
	//dbgprint ( "loadsector, read cache %d,"
	//			 " handle %d, offset %X",
	//		     freeinx, handle, secoffset ) ;
	result = wl_read ( handle, secoffset,				    // Read the sector
					   sectorbuf,
					   sizeof(sectorbuf) ) ;
	if ( result != ESP_OK )								          // Check result
	{
		dbgprint ( "wl_read failed from offset %X, "
				        "result = %d", secoffset, result ) ;
		return -1 ;
	}
	dcache[freeinx]->soffset = secoffset ;				  // Set flash offset for this entry
	dcache[freeinx]->handle = handle ;					    // Is now occupied
	dcache[freeinx]->atime = atime++ ;					    // Add the timestamp
	dcache[freeinx]->dirty = false ;					      // Sector not dirty yet
	pout = dcache[freeinx]->cbuf ;						      // Point to begin of dcache.cbuf
	pin = sectorbuf ;									              // Source pointer
	for ( i = 0 ; i < ( PPS * 128 ) ; i += 4 )			// Fill pages of 128 words in a sector
	{
		*pout++ = *pin & 07777 ;						          // Word 1, 12 bits
		wbuf = ( *pin++ & 0xF000 ) >> 12 ;				    // Put original bits 8-11 into place
		*pout++ = *pin & 07777 ;						          // Word 2, 12 bits
		wbuf |= ( *pin++ & 0xF000 ) >> 8 ;				    // Put original bits 4-7 into place
		*pout++ = *pin & 07777 ;						          // Word 3, 12 bits
		wbuf |= ( *pin++ & 0xF000 ) >> 4 ;				    // Put original bits 0-3 into place
		*pout++ = wbuf ;								              // Store word 4
	}
	return freeinx ;
}


//***********************************************************************************************
//										                    D S K R E A D											                    *
//***********************************************************************************************
// Read a number of pages from partition cache to memory.										                    *
//***********************************************************************************************
bool dskread ( wl_handle_t handle, uint16_t* wbuf, uint16_t blocknr, uint16_t npages )
{
	uint16_t	i ;										                // Loop control
	uint16_t	pnr ;									                // Page number
	uint32_t	secoffset ;								            // Offset in flash for sector
	uint16_t	ps ;									                // Position of page in sector
	int16_t		cs ;									                // Index in dcache

	pnr = blocknr * 2 ;									            // 2 pages in a block
	for ( i = 0 ; i < npages ; i++ )					      // Do all pages
	{
		secoffset = ( pnr / PPS ) * 4096 ;				    // Compute offset to begin of sector
		cs = loadsector ( handle, secoffset ) ;			  // Load sector in cache
		if ( cs < 0 )									                // Check result
		{
			return false ;								              // Read error!
		}
		ps = ( pnr % PPS ) * 128 ;						        // Offset in sector
		memcpy ( wbuf, &dcache[cs]->cbuf[ps], 256 ) ;	// Move 128 words of data to destination
		pnr++ ;										                  	// Next page
		wbuf += 128 ;
	}
	return true ;										                // Success
}


//***********************************************************************************************
//										                    D S K W R I T E											                  *
//***********************************************************************************************
// Write a number of pages from memory to partition cache.										                  *
//***********************************************************************************************
bool dskwrite ( wl_handle_t handle, uint16_t* wbuf, uint16_t blocknr, uint16_t npages )
{
	uint16_t	i ;										                // Loop control
	uint16_t	pnr ;									                // Page number
	uint32_t	secoffset ;								            // Offset in flash for sector
	uint16_t	ps ;									                // Position of page in sector
	int16_t		cs ;									                // Index in dcache

	pnr = blocknr * 2 ;									            // 2 pages in a block
	for ( i = 0 ; i < npages ; i++ )					      // Do all pages
	{
		secoffset = ( pnr / PPS ) * 4096 ;				    // Compute offset to begin of sector
		cs = loadsector ( handle, secoffset ) ;			  // Load sector in cache
		ps = ( pnr % PPS ) * 128 ;						        // Offset in sector
		//dbgprint ( "blk = %o, pnr = %o, "
		//		     "secoffset = %X, "
		//		     "bufoffset = %o",
		//		     blocknr, pnr, secoffset, ps ) ;
		if ( cs < 0 )									                // Check result
		{
			dbgprint ( "loadsector fail" ) ;
			return false ;
		}
		memcpy ( &dcache[cs]->cbuf[ps], wbuf, 256 ) ;	// Move 128 words of data to destination
		dcache[cs]->dirty = true ;						        // Sector in cache is dirty now
		wbuf += 128 ;									                // Point to next source page
		pnr++ ;											                  // Next page
	}
	return true ;										                // Success
}


//***********************************************************************************************
//									              B L O C K D R I V E R										                      *
//***********************************************************************************************
// Handle Read or wite requests for OS/8 block drivers.											                    *
// Caller address is in AC.  Points to 3 words parameters, error return, normal return.			    *
//***********************************************************************************************
void blockdriver ( wl_handle_t handle )
{
	uint16_t cadr ;											                // Caller parameter/return address
	uint16_t fcw ;											                // Function control word
	uint16_t xfer_df ;										              // Datafield for transfer
	uint16_t xfer_ma ;										              // Memory address for transfer
	uint16_t xfer_pages ;									              // Number of pages for transfer
	uint16_t xfer_block ;									              // Start block number for transfer

	cadr = AC ;												                  // Get address of parameters
	AC = 0 ;												                    // Clear AC and link
	fcw = MEM[DF][cadr++] ;									            // Get function control word
	xfer_pages = ( fcw >> 6 ) & 037 ;						        // Get number of pages
	if ( xfer_pages == 0 )									            // Zero means 40 octal pages
	{
		xfer_pages = 040 ;
	}
	xfer_df = ( fcw & 070 ) >> 3 ;							        // Get datafield
	xfer_ma = MEM[DF][cadr++] ;								          // Get memory address
	xfer_block = MEM[DF][cadr++] ;							        // And block number
	IF = DF ;												                    // Return to address in DF
	IFpending = IF ;										                // No more pending IF
	PC = cadr ;												                  // Points to normal return address
	//dbgprint ( "Transfer %s, "
	//			 "fcw:%04o, ma:%04o bl:%04o, "
	//			 "return to %d:%04d",
	//			 devicesx[handle].devname,
	//			 fcw, xfer_ma, xfer_block, IF, PC ) ;
	if ( handle != WL_INVALID_HANDLE )						      // Valid handle
	{
		if ( fcw & 04000 )									              // Write request?
		{
			if ( dskwrite ( handle, &MEM[xfer_df][xfer_ma],	// Write to device
					xfer_block, xfer_pages ) )
			{
				PC++ ;										                    // Normal return
			}
		}
		else
		{
			if ( dskread ( handle, &MEM[xfer_df][xfer_ma],	// Read from device
					xfer_block, xfer_pages ) )
			{
				PC++ ;										                    // Normal return
			}
		}
	}
}


//***********************************************************************************************
//										                    B O O T													                      *
//***********************************************************************************************
// Move block 0 of the SYS device into page 0 and 1 of field 0. Then the program starts at 0.	  *
//***********************************************************************************************
void boot()
{
	wl_handle_t hndl ;									          // Handle of system device (RKA0)

	hndl = devicesx[0].handle ;							      // Get device handle
	dbgprint ( "Booting OS/8" ) ;
	if ( dskread ( hndl, &MEM[0][0], 0, 2 ) )			// Read 1 block (2 pages)
	{
		for ( int i = 0 ; i < SZSYSHND ; i++ )			// Patch SYS handler, 18 words
		{
			MEM[0][0207+i] = ddr[i] ;					        // Starts at 07607
		}
		MEM[0][066] = os8date ;							        // Bootstrap will put date in 17666
		MEM[0][0377] = os8datex ;						        // Bootstrap will put ext date in 07777
	}
	else
	{
		dbgprint ( "Cannot read from RKA0" ) ;
	}
	AC = 0 ;											                // Clear AC and link
	DF = 0 ;											                // Set DF and IF to 0
	IF = 0 ;
	IFpending = 0 ;										            // NO pending IF
	PC = 00000 ;										              // Jump into stage 2 of bootstrap
	running = true ;									            // Start PDP8
}


//***********************************************************************************************
//										                  O P A D D R												                      *
//***********************************************************************************************
// Get effective address for Memory Reference Instructions.										                  *
// A pointer to the target location within MEM is returned.										                  *
//***********************************************************************************************
uint16_t* opAddr()										            // Get address specified by operand
{
	MA = IR & 0177 ;									              // Address in current page or page 0
	if ( IR & 0200 )									              // Current page?
	{
		MA |= ( PC - 1 ) & 07600 ;						        // Yes, add base page
	}
	if ( IR & 0400 )									              // Indirect?
	{
		if ( ( MA & 07770 ) == 010 )					        // Auto increment address (10..17)?
		{
			MEM[IF][MA] = ( MEM[IF][MA]+1 ) & 07777 ;   // Yes, increment pointer first
		}
		MA = MEM[IF][MA] ;								            // Load effective address
		MB = MEM[DF][MA] ;								            // MB for console display
		return &MEM[DF][MA] ;							            // Address in DF
	}
	MB = MEM[IF][MA] ;									            // MB for console display
	return &MEM[IF][MA] ;								            // Address in IF
}


//***********************************************************************************************
//										                    O P A D D R J											                    *
//***********************************************************************************************
// Get effective adress for JMP/JMS Instructions.												                        *
//***********************************************************************************************
uint16_t opAddrJ()										          // Get address specified by operand
{
	MA = IR & 0177 ;									            // Address in current page or page 0
	if ( IR & 0200 )									            // Current page?
	{
		MA |= ( PC - 1 ) & 07600 ;						      // Yes, add base page
	}
	if ( IR & 0400 )									            // Indirect?
	{
		if ( ( MA & 07770 ) == 010 )					      // Auto increment address (10..17)?
		{												                    // Although unlikely for JMP/JMS
			MEM[IF][MA] = ( MEM[IF][MA]+1 ) & 07777 ;	// Yes, increment pointer first
		}
		MA = MEM[IF][MA] ;								          // Load effective address
	}
	return MA ;											              // Address
}


//***********************************************************************************************
//											                  I O T												                          *
//***********************************************************************************************
// Handling of IOTs.																			                                      *
//***********************************************************************************************
void iot()
{
	wl_handle_t hndl ;									          // Handle for block driver
	uint16_t    c ;										            // Input/output character keyboard/ptp

	//vTaskDelay ( 0 ) ;									        //  call to keep RTOS happy
	switch ( IR & 07770 )
	{
	case 06200 :										              // Memory extension instructions?
	case 06210 :
	case 06220 :
	case 06230 :
	case 06240 :
	case 06250 :
	case 06260 :
	case 06270 :
		switch ( IR & 07707 )
		{
		case 06201 :									              // CDF
			DF = ( IR >> 3 ) & 07 ;
			break ;
		case 06202 :									              // CIF
			IFpending = ( IR >> 3 ) & 07 ;
			break ;
		case 06203 :									              // CIF CDF combination
			IFpending = ( IR >> 3 ) & 07 ;				    // delays one cycle
			DF = ( IR >> 3 ) & 07 ;
			break ;
		case 06204 :									              // Other memory extension instructions?
			switch ( IR )
			{
			case 06214 :								              // RDF
				AC |= ( DF << 3 ) ;						          // OR DF into bits 6-8 of the AC
				break ;
			case 06224 :								              // RIF
				AC |= ( IF << 3 ) ;						          // OR IF into bits 6-8 of the AC
				break ;
			case 06234 :								              // RIB
				AC |= SF ;								              // OR SF into bits 6-8 and 9-11 of the AC
				// ToDo: timeshare bit in AC5
				break ;
			case 06244 :								              // RMF
				IFpending = ( SF >> 3 ) & 07 ;			    // Restore IF
				DF        = SF & 07 ;					          // Restore SF
				// ToDo: timeshare bit
				break ;
			}
			break ;
			default :
				// OS/8 uses some strange IOTs.  Report them.
				dbgprint ( "IOT %04o at %o:%04o, AC=%04o\r\n", IR, IF, PC, AC & 07777 ) ;
				//running = false ;						          // Stop interpreting
		}
		break ;
	case 06000 :
		switch ( IR )
		{
		/*
		case 06000 :									              // SKON, skip if interrupt/turn interrupts off
			if ( IENA )									              // IENA set?
			{
				PC++ ;									                // Yes, skip
			}
			IENA = false ;								            // Turn interrupts off
			break ;
		case 06001 :									              // ION
			IENApending = true  ;						          // Enable interrupt, delayed one cycle
			break ;
		case 06002 :									              // IOF
			IENA = false ;
			break ;
		case 06003 :									              // SRQ
			break ;										                // Treat as a NOP
		case 06004 :									              // GTF
			t = AC ;									                // Save current AC
			AC = SF ;
			if ( t & 010000 )							            // Link set?
			{
				AC |= 04000 ;							              // Yes, link to AC0
			}
			if ( ( t & 04000 ) == 0 )					        // Greater than flag set?
			{
				AC |= 02000 ;							              // Yes, flag to AC1
			}
		*/
		case 06007 :									              // CAF
			AC = 0 ;									                // Clear AC and link
			break ;										                // To do: interrupt flags
		default :
			dbgprint ( "IOT %04o at %o:%04o, AC=%04o\r\n", IR, IF, PC, AC & 07777 ) ;
			//running = false ;							          // Stop interpreting
		}
		break ;
	case 06010 :										              // Paper tape reader
		if ( IR & 01 )									            // RSF
		{
			if ( PTReof )								              // EOF detected?
			{
				PTReof = false ;						            // Yes, reset flag
			}
			else if ( PTRhandle )						          // Input file already open?
			{
				PC++ ;									                // Yes, skip
			}
			else
			{
				PTRhandle = fopen ( PTRfile, "r" ) ;	  // Try to open the file
				if ( PTRhandle )						            // Opened now?
				{
					PC++ ;								                // Yes, skip
					dbgprint ( "PTR file %s opened for read",
							   PTRfile ) ;
				}
			}
		}
		if ( IR & 04 )									            // RFC
		{
			if ( PTRhandle )
			{
				PTRchar = getc ( PTRhandle ) ;			    // Get next character
				if ( PTRchar == 0177777 )				        // End of file?
				{
					PTRchar = 0232 ;					            // Send Ctrl-Z (EOF)
				}
				if ( PTRchar == 0232 )					        // EOF?
				{
					fclose ( PTRhandle ) ;				        // Close the file
					PTRhandle = NULL ;					          // And clear handle
					PTReof = true ;						            // For time-out detection
					dbgprint ( "PTR EOF" ) ;
				}
			}
			else
			{
				PTRchar = 0 ;							              // No input yet
				dbgprint ( "PTR read, no open file" ) ;
			}
		}
		if ( IR & 02 )									            // RRB
		{
			AC = PTRchar ;								            // Read character
		}
		break ;
	case 06020 :										              // Paper tape punch
		if ( IR & 01 )									            // PSF
		{
			if ( PTPhandle )							            // File correctly opened?
			{
				PC++ ;									                // Yes, skip
			}
		}
		if ( IR & 04 )									            // PPC
		{
			c = AC & 0377 ;								            // Get output character
			if ( PTPhandle == NULL )
			{
				PTPhandle = fopen ( PTPfile, "w" ) ;	  // Try to open the file
				if ( PTPhandle )						            // Opened now?
				{
					dbgprint ( "PTP file %s opened for write",
							   PTPfile ) ;
				}
			}
			if ( PTPhandle )
			{
				putc ( c, PTPhandle ) ;					        // Store the byte
				dbgprint ( "PTP punched %03o",
						   c ) ;
				if ( c == 0232 )						            // Ctrl-Z?
				{
					fclose ( PTPhandle ) ;				        // Close output
					PTPhandle = NULL ;					          // Handle useless
				}
			}
		}
		// PPC is ignored
		break ;
	case 06030 :										              // Keyboard
		if ( IR & 01 )									            // KSF, skip if ready
		{
			if ( kbd_available() )						        // Any input from telnet socket?
			{
				PC++ ;									                // Yes, skip
			}
			else
			{
				// Delay if "KSF;JMP .-1" is detected, probably most of the time.
				if ( MEM[IF][PC] == ( 05000 + ( ( PC - 1 ) & 0377 ) ) )
				{
					vTaskDelay ( 100 / portTICK_PERIOD_MS ) ;	//  100 msec
				}
			}
			break ;
		}
		if ( IR & 04 )									            // KRS, read byte and OR into AC
		{
			c = kbd_input() ;							            //
			if ( uppercase )							            // Convert to uppercase?
			{
				c = toupper ( c ) ;						          // Yes
			}
			AC = ( AC & 010000 ) | c | 0200 ;			    // Clear AC, OR character in, set bit 4
		}
		if ( IR & 02 )									            // KCC
		{
			kbd_clear() ;								              // and keyboard flag
		}
		break ;
	case 06040 :										              // Teleprinter like ASR33
		if ( IR & 01 )									            // TSF, skip if ready
		{
			if ( tls_space() )							          // See if space in the queue
			{
				PC++ ;									                // There is space, skip
			}
		}
		if ( IR & 04 )									            // Send byte?
		{
			tls_put ( AC & 0177 ) ;						        // Strip off parity and print
		}
		break ;
	case 06100 :										              // Memory parity option
		break ;											                // Treat as NOP, so SPO will not skip
	case 06300 :										              // 6301 appears in BATCH.SV
		break ;
	case 06550 :										              // FPP not supported
	case 06560 :										              // FPP not supported
		break ;
	case 06770 :										              // Block driver super IOT?
		switch ( IR )
		{
		case 06770 :									              // RKA0:
		case 06771 :									              // RKB0:
		case 06772 :									              // RKA1:
		case 06773 :									              // RKB1:
		case 06774 :									              // RKA2:
		case 06775 :									              // RKB2:
		case 06776 :									              // DTA0:
		case 06777 :									              // DTA1:
			hndl = devicesx[IR & 07].handle ;			    // Get the handle
			blockdriver ( hndl ) ;						        // Handle read/write block
			break ;
		default :
			dbgprint ( "Super IOT %04o "				      // IOT not yet supported
					   "at %o:%04o "
					   "not supported",
					   IR, IF, PC-1 ) ;
			//running = false ;							          // Stop interpreting
			break ;
		}
		break ;
		default :
			dbgprint ( "IOT %04o at %o:%04o, "			  // IOT not yet supported
					   "AC=%04o\r\n",
					   IR, IF, PC-1,
					   AC & 07777 ) ;
			//running = false ;							          // Stop interpreting
			break ;
	}
}


//***********************************************************************************************
//											                      O P R												                      *
//***********************************************************************************************
// Handling of Operate Microinstructions.														                            *
//***********************************************************************************************
void opr()
{
	if ( ( IR & 0400 ) == 0 )								            // group 1
	{
		if ( IR & 0200 )									                // CLA
		{
			AC &= 010000 ;
		}
		if ( IR & 0100 )									                // CLL
		{
			AC &= 07777 ;
		}
		if ( IR & 040 )										                // CMA
		{
			AC ^= 07777 ;
		}
		if ( IR & 020 )										                // CML
		{
			AC ^= 010000 ;
		}
		if ( IR & 01 )										                // IAC
		{
			AC = ( AC + 1 ) & 017777 ;
		}
		switch ( IR & 016 )
		{
		case 012 :											                  // RTR
			AC = ( ( AC >> 1 ) | ( AC << 12 ) ) & 017777 ;	// Fall through
		case 010 :											                  // RAR
			AC = ( ( AC >> 1 ) | ( AC << 12 ) ) & 017777 ;
			break ;
		case 06 :											                    // RTL
			AC = ( ( AC >> 12 ) | ( AC << 1 ) ) & 017777 ;	// Fall through
		case 04 :											                    // RAL
			AC = ( ( AC >> 12 ) | ( AC << 1 ) ) & 017777 ;
			break ;
		case 02 :											                    // BSW
			AC = ( AC & 010000 ) | ( ( AC >> 6 ) & 077 )
			| ( ( AC << 6 ) & 07700 ) ;
			break ;
		}
	}
	else if ( ( IR & 0401 ) == 0400 )
	{
		// SMA, SPA, SZA, SNA, SNL, SZL
		int s = ( ( IR & 0100 ) && ( AC & 04000 ) ) ||
				( ( IR & 040 ) && ( AC & 07777 ) == 0 ) ||
				( ( IR & 020 ) && ( AC & 010000 ) != 0 ) ? 0 : 010 ;
		if ( s == ( IR & 010 ) )
			PC++ ;
		if ( IR & 0200 )									                // CLA
			AC &= 010000 ;
		if ( IR & 04 )									                  // OSR
			AC |= SR ;
		if ( IR & 02 )									                  // HLT
		{
			printf ( "\n" ) ;
			dbgprint ( "HALT at IF=%o, PC=%04o, "
					"AC=%04o",
					IF, PC - 1, AC & 07777 ) ;
			running = false ;
		}
		if ( IR & 0200 )									                // CLA
		{
			AC &= 010000 ;
		}
		if ( IR & 04 )										                // OSR
		{
			AC |= SR ;
		}
		if ( IR & 02 )									                  // HLT
		{
			printf ( "\n" ) ;
			dbgprint ( "HALT at IF=%o, PC=%04o, "
					   "AC=%04o",
					IF, PC - 1, AC & 07777 ) ;
			running = false ;
		}
	}
	else													                      // Group 3
	{
		t = MQ ;
		if ( IR & 0200 )									                // CLA
		{
			AC &= 010000 ;
		}
		if ( IR & 020 )										                // MQL
		{
			MQ = AC & 07777 ;
			AC &= 010000 ;
		}
		if ( IR & 0100 )
		{
			AC |= t ;
		}
	}
}


//***********************************************************************************************
//											                    I N T E R P											                    *
//***********************************************************************************************
// Main loop of the application.																                                *
// Interpret n instructions in MEM or until a HLT is executed.									                *
//***********************************************************************************************
void interp ( int n )
{
	uint16_t* p ;											      // Effective address

	while ( ( n-- != 0 ) && running )
	{
		IR = MEM[IF][PC] ;									  // Get instruction register IR
		PC++ ;												        // Update PC
		PC &= 07777 ;										      // Wrap around
		instcount++ ;										      // Count number of instructions
		switch ( IR & 07000 )
		{
		case 00000 :										      // AND
			AC = AC & ( *opAddr() | 010000 ) ;	// And with operator, do not change link
			break ;
		case 01000 :										      // TAD
			AC = ( AC + *opAddr() ) & 017777 ;
			break ;
		case 02000 :										      // ISZ
			p = opAddr() ;									    // Get effective address
			*p = ( ( *p ) + 1 ) & 07777 ;				// Increment
			if ( *p == 0 )									    // Zero now?
			{
				PC++ ;										        // Yes, skip next instruction
				PC &= 07777 ;								      // Wrap around
			}
			break ;
		case 03000 :										      // DCA
			*opAddr() = AC & 07777 ;						// Deposit
			AC &= 010000 ;									    // CLA, do not touch link
			break ;
		case 04000 :										      // JMS
			t = opAddrJ() ;									    // Get effective address
			IF = IFpending ;								    // Set target IF
			MEM[IF][t] = PC ;								    // Store current PC in this location
			PC = ++t & 07777 ;								  // Goto subroutine address plus 1
			break ;
		case 05000 :										      // JMP
			PC = opAddrJ() ;								    // Set PC to effective address
			IF = IFpending ;								    // Set IF
			break ;
		case 06000 :										      // IOT
			iot() ;											        // Handle IOTs
			break;
		case 07000 :										      // OPR
			opr() ;											        // Handle operates
			break ;
		}
	}
}


//***********************************************************************************************
//								                    P D P 8 T A S K 			      									            *
//***********************************************************************************************
// Task to simulate the PDP8 processor.															                            *
// Most of the job is dome by "interp()".														                            *
//***********************************************************************************************
void pdp8Task ( void *pvParameter )
{
	vTaskDelay ( 2000 / portTICK_PERIOD_MS ) ;				// Sleep some time
	obtain_time() ;											              // Get current time
	while ( true )
	{
		lc_sim++ ;											                // Count number of loops
		interp ( 200 ) ;									              // Emulate next 200 instruction
		if ( flushrequest )									            // Request to flush?
		{
			flushcache() ;									              // Yes, do it
			flushrequest = false ;							          // Clear request
		}
    //		yield() ;									                // Allow others
	}
}


//***************************************************************************************************
//                                      S T A C K D U M P	                                          *
//***************************************************************************************************
// Dump the various stacks for debugging purpose.                                                   *
//***************************************************************************************************
void stackDump()
{
	const char*  nstr  = "Free stack of %-13s is %4d, "			// Format string for task info
						 "run count is %10d" ;

	dbgprint ( nstr,											                  // Stack usage, loop count
			   pcTaskGetTaskName ( NULL ),						          // for main task
			   uxTaskGetStackHighWaterMark ( NULL ),
			   lc_main ) ;
	dbgprint ( nstr,											                  // Stack usage, loop count
			   pcTaskGetTaskName ( th_telnet ),					        // for telnet task
			   uxTaskGetStackHighWaterMark ( th_telnet ),
			   lc_telnet ) ;
	dbgprint ( nstr,											                  // Stack usage, loop count
			   pcTaskGetTaskName ( th_sim ),					          // for simulator task
			   uxTaskGetStackHighWaterMark ( th_sim ),
			   lc_sim ) ;
	dbgprint ( nstr,											                  // Stack usage, loop count
			   pcTaskGetTaskName ( th_user ),					          // for user task
			   uxTaskGetStackHighWaterMark ( th_user ),
			   lc_user ) ;
	#ifdef OLEDDISPLAY
		dbgprint ( nstr,										                  // Stack usage, loop count
				   pcTaskGetTaskName ( th_console ),			        // for console task
				   uxTaskGetStackHighWaterMark ( th_console ),
				   lc_console ) ;
	#endif
	dbgprint ( "Free heap space is %6d bytes",
				esp_get_free_heap_size() ) ;
	dbgprint ( "Menu state is %d, run state is %d", menu_state, running ) ;
}


//***********************************************************************************************
//											                    S E T U P											                      *
//***********************************************************************************************
//* Started by bootloader.																		                                  *
//***********************************************************************************************
void setup()
{
	uint16_t		flushcount = 0 ;						          // Timer for flushing cache
	esp_err_t		ret ;									                // Result card mount
	uint8_t			wake_up_pin = 0 ;						          // Pin 0 used for wake-up
	dcache_t*		p ;										                // Pointer to allocated cache space

	Serial.begin ( 115200 ) ;								          // Init serial output
  delay ( 3000 ) ;										              // Start delay
	Serial.println() ;
  dbgsem  = xSemaphoreCreateMutex() ;						    // Semaphore for exclusive use of dbgprint
  #ifdef OTA
    ota_enabled = true ;                            // Enable OTA if defined
  #endif
	//esp_sleep_pd_config ( ESP_PD_DOMAIN_RTC_PERIPH,	// Init deep-sleep mode
	//					  ESP_PD_OPTION_AUTO ) ;
	//esp_sleep_enable_ext0_wakeup ( (gpio_num_t)wake_up_pin,	// Wake if GPIO is low
	//							   0 ) ;		
	pinMode ( wake_up_pin, INPUT_PULLUP ) ;					  // Use pull-up on GPIO 0 (wake-up)
	pinMode ( SD_CS, OUTPUT ) ;								        // CS pin for SD card is output
	if ( RST_PIN >= 0 )
	{
	  pinMode ( RST_PIN, OUTPUT ) ;							      // Reset pin for OLED is output
	  digitalWrite ( RST_PIN, HIGH ) ;						        // Reset pin for OLED must be HIGH
	}
	dbgprint ( "Starting PDP8 simulator on ESP32..." ) ;
	dbgprint ( "Flash size is %d MB", 						        // Show flash size
	           ESP.getFlashChipSize() / 1048576 ) ;
    Wire.begin ( SDA_PIN, SCL_PIN, (uint32_t)400000 ) ;	// For possible display
	i2cScan() ;												// TEST*TEST*TEST
	SPI.begin ( SD_SCK, SD_MISO, SD_MOSI, SD_CS ) ;
	card_okay = SD.begin ( SD_CS, SPI, 4000000 ) ;		    // Check SD mount result
	if ( !card_okay )
	{
		if ( ret == ESP_FAIL )
		{
			dbgprint ( "Failed to mount filesystem!" ) ;
		}
		else
		{
			dbgprint ( "Failed to initialize SD card (%d).", ret ) ;
		}
	}
	else
  {
    card_okay = ( SD.cardType() != CARD_NONE ) ;        // See if known card
    if ( ! card_okay )
    {
      dbgprint ( "No SD card attached" ) ;              // Card not readable
    }
  }
  if ( ota_enabled )                                    // OTA configured?
  {
    if ( ! esp_partition_find (                         // Get partition iterator for
                  ESP_PARTITION_TYPE_APP,               // OTA partition
                  ESP_PARTITION_SUBTYPE_APP_OTA_0,
                  NULL  ) )
    {
      ota_enabled = false ;                             // No OTA partition, disable OTA handling
    }
  }
	initialize_wifi() ;										                // Initialize WiFi
	if ( ota_enabled )
  {
    ArduinoOTA.setHostname ( NAME ) ;						        // Set the hostname
    ArduinoOTA.begin() ;									              // Allow update over the air
  }
	for ( int i = 0 ; i < NUMDEV ; i++ )					        // Mount all device partitions
	{
	  dvmount ( &devicesx[i].handle, devicesx[i].devname,
			  	devicesx[i].size ) ;
	}
	if ( card_okay )
	{
		dbgprint ( "SD card found, ready for use" ) ;
	}
	for ( int i = 0 ; i < CACHESIZE ; i++ )
	{
		p = (dcache_t*)calloc ( 1, sizeof(dcache_t) ) ;		  // Allocate space for one cache buffer
		dcache[i] = p ;										                  // Save pointer to buffer
		dcache[i]->handle = ILLHANDLE ;						          // Set handle to unused
	}
	for ( int i = 0 ; i < 8 ; i++ )
	{
		for ( int j = 0 ; j < 4096 ; j++ )
		{
			MEM[i][j] = 07402 ;								                // Init pdp8 memory to all HLTs
		}
	}
	dbgprint ( "Starting PDP8 Emulator task "
			   "and telnet server" ) ;
 	kbd_queue = xQueueCreate( 512, sizeof(uint8_t) ) ;	  // Init 2 queues
	tls_queue = xQueueCreate( 512, sizeof(uint8_t) ) ;	  // for input and output

	xTaskCreatePinnedToCore (								              // Create task
		pdp8Task, 											                    // Task module.
		"PDP8Task",										                      // Name of task.
		2200,												                        // Stack size of task
		NULL,												                        // No parameters
		tskIDLE_PRIORITY,									                  // priority
		&th_sim,											                      // Task handle
		0 ) ;												                        // Run on CPU 0
	xTaskCreatePinnedToCore (								              // Create task
		telnetTask,   										                  // Task module.
		"telnetTask",   									                  // Name of task.
		2200,												                        // Stack size of task
		NULL,												                        // No parameters
		3,													                        // priority
		&th_telnet,											                    // Task handle
		0 ) ;												                        // Run on CPU 0
	xTaskCreatePinnedToCore (								              // Create task
		userTask,   										                    // Task module.
		"userTask",   									                    // Name of task.
		2200,												                        // Stack size of task
		NULL,												                        // No parameters
		3,													                        // priority
		&th_user, 											                    // Task handle
		0 ) ;												                        // Run on CPU 0
	#ifdef OLEDDISPLAY
		xTaskCreatePinnedToCore (							              // Create task
			consoleTask,									                    // Task module.
			"consoleTask",										                // Name of task.
			2200,											                        // Stack size of task
			NULL,											                        // No parameters
			2,												                        // priority
			&th_console,									                    // Task handle
			0 ) ;											                        // Run on CPU 0
	#endif
	dbgprint ( "End of setup()" ) ;
}


//***********************************************************************************************
//											                    L O O P												                      *
//***********************************************************************************************
//* Main loop of the program.																	                                  *
//***********************************************************************************************
void loop()
{
	static uint32_t lasttim = 0 ;
	uint32_t        newtim ;
	static uint16_t	show_stack = 59 ;					// Counter for showing stack space
	static uint16_t flushcount = 0 ;					// Timer for flushing cache

  newtim = millis() ;									      // Get current time
	lc_main++ ;											          // Count number of loops
	if ( ota_enabled )
  {
      ArduinoOTA.handle() ;							    // Check for OTA actions
  }
	if ( newtim < ( lasttim + 10000 ) )				// 10 seconds passed?
	{
		return ;										            // No, quick return
	}
	// 10 seconds has passed
	lasttim = newtim ;
	if ( ++show_stack == 60 )							    // Time to show stacks every 5 minutes?
	{
    stackDump() ;    									      // Yes, show memory usage
		show_stack = 0 ;								        // Reset counter
	}
	if ( instcount )
	{
		dbgprint ( "Number of instructions processed:  %d/sec, "
				       "PC is %o:%04o",
				       instcount/ 10, IF, PC ) ;
		instcount = 0 ;									        // Reset instruction counter
	}
	if ( flushcount++ >= 30 )							    // Time to flush the cache buffers?
	{
		flushcount = 0 ;								        // Yes, reset counter
		flushrequest = true ;							      // Request a flush
	}
	if ( ( !apmode ) &&
	     ( WiFi.status() != WL_CONNECTED ) )
	{
		dbgprint ( "Reconnect to WiFi.." ) ;
		WiFi.reconnect() ;
	}
  if ( digitalRead ( 0 ) == LOW )           // Stackdump request?
  {
    delay ( 200 ) ;                         // Yes, debounce
    stackDump() ;                           // Show stack usage
  }
}
