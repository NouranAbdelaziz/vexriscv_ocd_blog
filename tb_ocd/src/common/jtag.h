
#include <stdio.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <string.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <sys/ioctl.h>
#include <netinet/tcp.h>

#include <iostream>
#include <fstream>

/** Returns true on success, or false if there was an error */
bool SetSocketBlockingEnabled(int fd, bool blocking)
{
   if (fd < 0) return false;

#ifdef WIN32
   unsigned long mode = blocking ? 0 : 1;
   return (ioctlsocket(fd, FIONBIO, &mode) == 0) ? true : false;
#else
   int flags = fcntl(fd, F_GETFL, 0);
   if (flags < 0) return false;
   flags = blocking ? (flags&~O_NONBLOCK) : (flags|O_NONBLOCK);
   return (fcntl(fd, F_SETFL, flags) == 0) ? true : false;
#endif
}

class Jtag : public TimeProcess{
public:
	//CData *tms, *tdi, *tdo, *tck;
	//CData *RX, *TX;
	CData *jtag_in, *jtag_out, *tx_start, *tx_done, *rx_done, *send_to_ocd ;
	enum State {reset};
	uint32_t state;

	int serverSocket, clientHandle;
	struct sockaddr_in serverAddr;
	struct sockaddr_storage serverStorage;
	socklen_t addr_size;
	uint64_t tooglePeriod;

	ofstream LogFile;
//	char buffer[1024];

	//Jtag(CData *tms, CData *tdi, CData *tdo, CData* tck,uint64_t period){
	//Jtag(CData *RX, CData *TX, uint64_t period){
	Jtag(CData *jtag_in, CData *jtag_out, CData* tx_start, CData* tx_done, CData* rx_done, CData* send_to_ocd, uint64_t period){
		/*this->tms = tms;
		this->tdi = tdi;
		this->tdo = tdo;
		this->tck = tck;*/
		/*this->RX = RX;
		this->TX = TX;*/
		this-> jtag_in = jtag_in;
		this-> jtag_out = jtag_out;
		this-> tx_start = tx_start;
		this-> tx_done = tx_done;
		this-> rx_done = rx_done;
		this-> send_to_ocd = send_to_ocd;
		this->tooglePeriod = period/2;

		
		
		
		/**tms = 0;
		*tdi = 0;
		*tdo = 0;
		*tck = 0;*/
		/**TX = 0;
		*RX = 0;*/
		*jtag_in = 0;
		*jtag_out = 0;
		*tx_start = 0;
		*tx_done = 0;
		*rx_done = 0;
		*send_to_ocd = 0;
		state = 0;
		schedule(0);

		//---- Create the socket. The three arguments are: ----//
		// 1) Internet domain 2) Stream socket 3) Default protocol (TCP in this case) //
		serverSocket = socket(PF_INET, SOCK_STREAM, 0);
		assert(serverSocket != -1);
		int flag = 1;
		setsockopt(  serverSocket,            /* socket affected */
					 IPPROTO_TCP,     /* set option at TCP level */
					 TCP_NODELAY,     /* name of option */
					 (char *) &flag,  /* the cast is historical
											 cruft */
					 sizeof(int));    /* length of option value */

		/*int a = 0xFFF;
		if (setsockopt(serverSocket, SOL_SOCKET, SO_RCVBUF, &a, sizeof(int)) == -1) {
		    fprintf(stderr, "Error setting socket opts: %s\n", strerror(errno));
		}
		a = 0xFFFFFF;
		if (setsockopt(serverSocket, SOL_SOCKET, SO_SNDBUF, &a, sizeof(int)) == -1) {
		    fprintf(stderr, "Error setting socket opts: %s\n", strerror(errno));
		}*/

		SetSocketBlockingEnabled(serverSocket,0);


		//---- Configure settings of the server address struct ----//
		// Address family = Internet //
		serverAddr.sin_family = AF_INET;
		serverAddr.sin_port = htons(7894);
		serverAddr.sin_addr.s_addr = inet_addr("127.0.0.1");
		memset(serverAddr.sin_zero, '\0', sizeof serverAddr.sin_zero);

		//---- Bind the address struct to the socket ----//
		bind(serverSocket, (struct sockaddr *) &serverAddr, sizeof(serverAddr));

		//---- Listen on the socket, with 5 max connection requests queued ----//
		listen(serverSocket,1);

		//---- Accept call creates a new socket for the incoming connection ----//
		addr_size = sizeof serverStorage;
		clientHandle = -1;
		

	}
	void connectionReset(){
		printf("CONNECTION RESET\n");
		shutdown(clientHandle,SHUT_RDWR);
		clientHandle = -1;
	}


	virtual ~Jtag(){
		if(clientHandle != -1) {
			shutdown(clientHandle,SHUT_RDWR);
			usleep(100);
		}
		if(serverSocket != -1) {
			close(serverSocket);
			usleep(100);
		}
	}

	uint32_t selfSleep = 0;
	uint32_t checkNewConnectionsTimer = 0;
	uint8_t rxBuffer[100];
	int32_t rxBufferSize = 0;
	int32_t rxBufferRemaining = 0;

	int32_t count =0;
	uint8_t bit_num = 0;
	bool send_flag = false;
	bool start_tx = true;
	bool toggle = true;
	uint8_t buffer;
	uint8_t prev_buffer;

	virtual void tick(){
		
		checkNewConnectionsTimer++;
		if(checkNewConnectionsTimer == 5000){
			checkNewConnectionsTimer = 0;
			int newclientHandle = accept(serverSocket, (struct sockaddr *) &serverStorage, &addr_size);
			if(newclientHandle != -1){
				if(clientHandle != -1){
					connectionReset();
				}
				clientHandle = newclientHandle;
				printf("CONNECTED\n");
			}
			else{
				if(clientHandle == -1)
					selfSleep = 1000;
			}
		}
		if(selfSleep)
			selfSleep--;
		else{
			if(clientHandle != -1){
				
				int n;

				if(rxBufferRemaining == 0){
					if(ioctl(clientHandle,FIONREAD,&n) != 0)
						connectionReset();
					else if(n >= 1){
						rxBufferSize = read(clientHandle,&rxBuffer,100);
						cout << "RX buffer size is: " << rxBufferSize << endl;
						LogFile.open("LogFile.txt", std::ofstream::app);
							if(!LogFile){
								cout << "Could'nt open log file !"<<endl;
							}
						LogFile << "RX buffer size is: " << rxBufferSize << endl;
						LogFile.close();
						if(rxBufferSize < 0){
							connectionReset();
						}else {
							rxBufferRemaining = rxBufferSize;
						}
					}else {
						selfSleep = 30;
					}
				}
				
				
				//if(count <= 3000){
				if(*rx_done ==1 || start_tx ) {
					//count++;
					//cout << "rx is done "<<endl;
					start_tx = false;
					if(rxBufferRemaining != 0){

						buffer = rxBuffer[rxBufferSize - (rxBufferRemaining--)];
						*jtag_in = buffer;
						*tx_start = 1;

						cout << "buffer value is: " << unsigned(buffer) << endl;
							//LogFile << "Files can be tricky, but it is fun enough!"<<endl;
						LogFile.open("LogFile.txt", std::ofstream::app);
							if(!LogFile){
								cout << "Could'nt open log file !"<<endl;
							}
						LogFile << "buffer value is: " << unsigned(buffer) << endl;

						

						if(buffer & 4){
							buffer = *jtag_out;
							cout << "Sending buffer value from tdoooo : " << unsigned(buffer) << endl;
							LogFile << "Sending buffer value from tdoooo : " << unsigned(buffer) << endl;
							if(-1 == send(clientHandle,&buffer,1,0))
								connectionReset();
						}
							
					}
				}
				else if(!start_tx){
					*tx_start = 0;
				}

				//}
			}
		}
		schedule(tooglePeriod);

		LogFile.close();
	}

	

};