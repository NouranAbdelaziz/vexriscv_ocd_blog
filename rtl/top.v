module top(
    input  wire     clk,
    //input wire      rstn,
    input  wire     button,
    output wire     led0,
    output wire     led1,
    output wire     led2,

    input [7:0]       jtag_in_buffer,
    input wire        tx_start,
    output wire       tx_done,
    output wire       rx_done,
    output [7:0]      jtag_out_buffer,
    output wire       send_to_ocd
);
    wire tck, tms, tdi;
    reg tdo;
    reg rstn, reset;
    reg   [7:0]         reset_vec = 8'hff;

    always @(posedge clk) begin
        reset_vec       <= { reset_vec[6:0], 1'b0 };     
    end

    always @(posedge clk) begin
        reset  <= reset_vec[7];
    end

    assign rstn = ~reset;

    /*assign tms = ((jtag_in_buffer & 8'h01)!= 8'h00);
    assign tdi = ((jtag_in_buffer & 8'h02)!= 8'h00);
    assign tck = ((jtag_in_buffer & 8'h08)!= 8'h00);
    assign jtag_out_buffer = tdo;*/

    reg uart_RX, uart_TX;
    wire b_tick;
    //wire rx_done;
    //wire tx_done;
    
    //Baudrate = CLK_Freq/((Prescaler+1)*16)
    //Prescaler = CLK_Freq/(16*Baudrate) - 1

    // 12 MHz
    // baud = 128000 --> prescaler = 5 
    // baud = 250000 --> prescaler = 2

    // 100 MHz
    // baud = 1228800 --> prescaler = 4
    // baud = 1562500 --> prescaler = 3
    // baud = 2083333.3333 --> prescaler = 2
    // baud = 3125000 --> prescaler = 1

    // 300 MHz
    // baud = 6250000 --> prescaler = 2

    //  



    assign send_to_ocd = (jtag_in_buffer & 4) ? 1'b1 : 1'b0;

    BAUDGEN uBAUDGEN(
        .clk(clk),
        .rst_n(rstn),
        .prescale(16'd1),
        .en(1'b1),
        .baudtick(b_tick)
    );

    /*reg [2:0] i;

    always @ (posedge clk or negedge rstn)
    begin
      if(!rstn)
        i <= 0;
      else begin
      uart_RX <= jtag_in_buffer[i];
      //uart_RX <= ~ uart_RX;
      i <= i + 1;
      end 
    end */

    UART_RX uUART_RX(
        .clk(clk),
        .resetn(rstn),
        .b_tick(b_tick),
        .rx(uart_RX),
        .rx_done(rx_done),
        .dout(jtag_out_buffer)
    );


    //wire tdo_out;

    //assign jtag_out_buffer = tdo_out;

    UART_TX uUART_TX(
        .clk(clk),
        .resetn(rstn),
        .tx_start(tx_start), //???
        .b_tick(b_tick),
        .d_in(jtag_in_buffer),
        .tx_done(tx_done),
        .tx(uart_TX)
    );

    UART_JTAG_CONV #(.PRESCALE(1)) UM  
    (   .clk(clk),
        .rstn(rstn),
        .RX(uart_TX),
        .TX(uart_RX),
        //output
        .tck(tck),
        .tms(tms),
        .tdi(tdi),
        //input
        .tdo(tdo)
    );
    top_core top_c(
        .clk(clk),
        //input
        .jtag_tck(tck),
        .jtag_tms(tms),
        .jtag_tdi(tdi),
        //output
        .jtag_tdo(tdo),
        .led0(led0),
        .led1(led1),
        .led2(led2),
        .button(button)
    );

endmodule

module UART_JTAG_CONV #(parameter [15:0] PRESCALE=51) 
(   
    input wire          clk,
    input wire          rstn,

    // UART interface 
    input wire          RX,
    output wire         TX,

    //JTAG interface 
    output reg        tck,
    output reg        tms,
    output reg        tdi,
    input             tdo

); 
    
    wire        b_tick;
    wire        rx_done;
    wire        tx_done;

    wire [7:0]  tx_data;
    wire [7:0]  rx_data;

    reg         tx_start;


    always @ (posedge clk or negedge rstn)
      begin
        if(!rstn) begin
            tms <=1'b0;
            tdi <=1'b0;
            tck <=1'b0;
            tx_start <= 0;
            //tx_data <= 0;
        end 
       else if(rx_done)
        begin 
          tms <= ((rx_data & 8'h01)!= 8'h00);
          tdi <= ((rx_data & 8'h02)!= 8'h00);
          tck <= ((rx_data & 8'h08)!= 8'h00);
          tx_start <= 1'b1;
        end 
        else 
          tx_start<= 1'b0;
      end 
    
    assign tx_data = {7'b0,tdo};
    
    /*always @ (posedge clk or negedge rstn or posedge rx_done)
    begin
      if(!rstn) 
      begin
        tx_start <= 0;
        tx_data <= 0;
      end
      else 
      begin 
      if (rx_done)
      begin 
        if(((rx_data & 8'd4) != 8'd0))
          tx_data <= {7'b0,tdo};
          tx_start <= 1'b1;
      end 
      else 
        tx_start <=0;
      end 
    end */

    BAUDGEN uBAUDGEN(
        .clk(clk),
        .rst_n(rstn),
        .prescale(PRESCALE),
        .en(1'b1),
        .baudtick(b_tick)
    );

    UART_RX uUART_RX(
        .clk(clk),
        .resetn(rstn),
        .b_tick(b_tick),
        .rx(RX),
        .rx_done(rx_done),
        .dout(rx_data)
    );

    UART_TX uUART_TX(
        .clk(clk),
        .resetn(rstn),
        .tx_start(tx_start), //???
        .b_tick(b_tick),
        .d_in(tx_data),
        .tx_done(tx_done),
        .tx(TX)
    );


endmodule


// Baudrate = Clk/((prescale+1)*16)
// 19200 = 50,000,000 / ((prescale+1)*16)
// prescale = 161.76 ==> 162
module BAUDGEN
(
  input wire clk,
  input wire rst_n,
  input wire [15:0] prescale, 
  input wire en,
  output wire baudtick
);

reg [15:0] count_reg;
wire [15:0] count_next;

//Counter
always @ (posedge clk, negedge rst_n)
  begin
    if(!rst_n)
      count_reg <= 0;
    else if(en)
      count_reg <= count_next;
end

assign count_next = ((count_reg == prescale) ? 0 : count_reg + 1'b1);
assign baudtick = ((count_reg == prescale) ? 1'b1 : 1'b0);

endmodule


module UART_RX(
  input wire clk,
  input wire resetn,
  input wire b_tick,        //Baud generator tick
  input wire rx,            //RS-232 data port
  
  output reg rx_done,       //transfer completed
  output wire [7:0] dout    //output data
);

//STATE DEFINES  
  localparam [1:0] idle_st = 2'b00;
  localparam [1:0] start_st = 2'b01;
  localparam [1:0] data_st = 2'b11;
  localparam [1:0] stop_st = 2'b10;

//Internal Signals  
  reg [1:0] current_state;
  reg [1:0] next_state;
  reg [3:0] b_reg; //baud-rate/over sampling counter
  reg [3:0] b_next;
  reg [2:0] count_reg; //data-bit counter
  reg [2:0] count_next;
  reg [7:0] data_reg; //data register
  reg [7:0] data_next;
  
//State Machine  
  always @ (posedge clk, negedge resetn)
  begin
    if(!resetn)
      begin
        current_state <= idle_st;
        b_reg <= 0;
        count_reg <= 0;
        data_reg <=0;
      end
    else
      begin
        current_state <= next_state;
        b_reg <= b_next;
        count_reg <= count_next;
        data_reg <= data_next;
      end
  end

//Next State Logic 
  always @*
  begin
    next_state = current_state;
    b_next = b_reg;
    count_next = count_reg;
    data_next = data_reg;
    rx_done = 1'b0;
        
    case(current_state)
      idle_st:
        if(~rx)
          begin
            next_state = start_st;
            b_next = 0;
          end
          
      start_st:
        if(b_tick)
          if(b_reg == 7)
            begin
              next_state = data_st;
              b_next = 0;
              count_next = 0;
            end
          else
            b_next = b_reg + 1'b1;
            
      data_st:
        if(b_tick)
          if(b_reg == 15)
            begin
              b_next = 0;
              data_next = {rx, data_reg [7:1]};
              if(count_next ==7) // 8 Data bits
                next_state = stop_st;
              else
                count_next = count_reg + 1'b1;
            end
          else
            b_next = b_reg + 1;
            
      stop_st:
        if(b_tick)
          if(b_reg == 15) //One stop bit
            begin
              next_state = idle_st;
              rx_done = 1'b1;
            end
          else
           b_next = b_reg + 1;
    endcase
  end
  
  assign dout = data_reg;
  
endmodule

module UART_TX(
  input wire clk,
  input wire resetn,
  input wire tx_start,        
  input wire b_tick,          //baud rate tick
  input wire [7:0] d_in,      //input data
  output reg tx_done,         //transfer finished
  output wire tx              //output data to RS-232
  );
  
    //STATE DEFINES  
    localparam [1:0] idle_st = 2'b00;
    localparam [1:0] start_st = 2'b01;
    localparam [1:0] data_st = 2'b11;
    localparam [1:0] stop_st = 2'b10;
  
    //Internal Signals  
    reg [1:0] current_state;
    reg [1:0] next_state;
    reg [3:0] b_reg;          //baud tick counter
    reg [3:0] b_next;
    reg [2:0] count_reg;      //data bit counter
    reg [2:0] count_next;
    reg [7:0] data_reg;       //data register
    reg [7:0] data_next;
    reg tx_reg;               //output data reg
    reg tx_next;
  
//State Machine  
  always @(posedge clk, negedge resetn)
  begin
    if(!resetn)
      begin
        current_state <= idle_st;
        b_reg <= 0;
        count_reg <= 0;
        data_reg <= 0;
        tx_reg <= 1'b1;
      end
    else
      begin
        current_state <= next_state;
        b_reg <= b_next;
        count_reg <= count_next;
        data_reg <= data_next;
        tx_reg <= tx_next;
      end
  end


//Next State Logic  
  always @*
  begin
    next_state = current_state;
    tx_done = 1'b0;
    b_next = b_reg;
    count_next = count_reg;
    data_next = data_reg;
    tx_next = tx_reg;
    
    case(current_state)
      idle_st:
      begin
        tx_next = 1'b1;
        if(tx_start)
        begin
          next_state = start_st;
          b_next = 0;
          data_next = d_in;
        end
      end
      
      start_st: //send start bit
      begin
        tx_next = 1'b0;
        if(b_tick)
          if(b_reg==15)
            begin
              next_state = data_st;
              b_next = 0;
              count_next = 0;
            end
          else
            b_next = b_reg + 1;
      end
      
      data_st: //send data serially
      begin
        tx_next = data_reg[0];
        
        if(b_tick)
          if(b_reg == 15)
            begin
              b_next = 0;
              data_next = data_reg >> 1;
              if(count_reg == 7)    //8 data bits
                next_state = stop_st;
              else
                count_next = count_reg + 1;
            end
          else
            b_next = b_reg + 1;
      end
      
      stop_st: //send stop bit
      begin
        tx_next = 1'b1;
        if(b_tick)
          if(b_reg == 15)   //one stop bit
            begin
              next_state = idle_st;
              tx_done = 1'b1;
            end
          else
            b_next = b_reg + 1;
      end
    endcase
  end
  
  assign tx = tx_reg;
  
endmodule

`default_nettype none

// Comment out the line below to disable JTAG functionality.
`define JTAG_ENABLED

module top_core(
        input  wire     clk,
        input  wire     button,
        output reg      led0,
        output reg      led1,
        output reg      led2,

        input  wire     jtag_tck,
        input  wire     jtag_tms,
        input  wire     jtag_tdi,
        output wire     jtag_tdo
    );

    wire                iBus_cmd_valid;
    wire                iBus_cmd_ready;
    wire  [31:0]        iBus_cmd_payload_pc;

    reg                 iBus_rsp_valid;
    reg                 iBus_rsp_payload_error;
    reg   [31:0]        iBus_rsp_payload_inst;

    wire                dBus_cmd_valid;
    wire                dBus_cmd_ready;
    wire                dBus_cmd_payload_wr;
    wire  [31:0]        dBus_cmd_payload_address;
    wire  [31:0]        dBus_cmd_payload_data;
    wire  [1:0]         dBus_cmd_payload_size;

    reg                 dBus_rsp_ready;
    wire                dBus_rsp_error;
    wire  [31:0]        dBus_rsp_data;

    wire                reqCpuReset;

    reg   [7:0]         reset_vec = 8'hff;
    reg                 reset, reset_cpu;

    // 8 clock cycles of active-high reset.
    always @(posedge clk) begin
        reset_vec       <= { reset_vec[6:0], 1'b0 };     
    end

    always @(posedge clk) begin
        reset       <= reset_vec[7];
        reset_cpu   <= reset_vec[7] || reqCpuReset;
    end

    VexRiscvWithDebug u_vex (
            .clk                        (clk),
            .reset                      (reset_cpu),

            .io_iBus_cmd_valid          (iBus_cmd_valid),
            .io_iBus_cmd_ready          (iBus_cmd_ready),
            .io_iBus_cmd_payload_pc     (iBus_cmd_payload_pc),

            .io_iBus_rsp_valid          (iBus_rsp_valid),
            .io_iBus_rsp_payload_error  (iBus_rsp_payload_error),
            .io_iBus_rsp_payload_inst   (iBus_rsp_payload_inst),

            .io_dBus_cmd_valid          (dBus_cmd_valid),
            .io_dBus_cmd_ready          (dBus_cmd_ready),
            .io_dBus_cmd_payload_wr     (dBus_cmd_payload_wr),
            .io_dBus_cmd_payload_address(dBus_cmd_payload_address),
            .io_dBus_cmd_payload_data   (dBus_cmd_payload_data),
            .io_dBus_cmd_payload_size   (dBus_cmd_payload_size),

            .io_dBus_rsp_ready          (dBus_rsp_ready),
            .io_dBus_rsp_error          (dBus_rsp_error),
            .io_dBus_rsp_data           (dBus_rsp_data),

            .io_timerInterrupt          (1'b0),
            .io_externalInterrupt       (1'b0),

            .io_reqCpuReset             (reqCpuReset),

`ifdef JTAG_ENABLED
            .io_jtag_tck                (jtag_tck),
            .io_jtag_tms                (jtag_tms),
            .io_jtag_tdi                (jtag_tdi),
            .io_jtag_tdo                (jtag_tdo)
`else
            .io_jtag_tck                (1'b0),
            .io_jtag_tms                (1'b1),
            .io_jtag_tdi                (1'b1),
            .io_jtag_tdo                ()
`endif
        );

    // When changing this value, checkout ./sw/Makefile for a list of 
    // all other files that must be changed as well.
    localparam mem_size_bytes   = 4096;
    localparam mem_addr_bits    = 12;

    reg [7:0] mem0[0:mem_size_bytes/4-1];
    reg [7:0] mem1[0:mem_size_bytes/4-1];
    reg [7:0] mem2[0:mem_size_bytes/4-1];
    reg [7:0] mem3[0:mem_size_bytes/4-1];

    initial begin
        // Either `define SEMIHOSTING_SW in this file, or specify it in your
        // synthesis tool. E.g. in Quartus you can define it under 
        // Settings -> Compiler Settings -> Verilog HDL Input -> Verilog HDL macro
`ifdef SEMIHOSTING_SW
        $readmemh("../sw_semihosting/progmem0.hex", mem0);
        $readmemh("../sw_semihosting/progmem1.hex", mem1);
        $readmemh("../sw_semihosting/progmem2.hex", mem2);
        $readmemh("../sw_semihosting/progmem3.hex", mem3);
`else
        $readmemh("../sw/progmem0.hex", mem0);
        $readmemh("../sw/progmem1.hex", mem1);
        $readmemh("../sw/progmem2.hex", mem2);
        $readmemh("../sw/progmem3.hex", mem3);
`endif
    end

    assign iBus_cmd_ready           = 1'b1;

    assign dBus_cmd_ready           = 1'b1;
    assign dBus_rsp_error           = 1'b0;

    wire [31:0] dBus_wdata;
    assign dBus_wdata = dBus_cmd_payload_data;

    wire [3:0] dBus_be;
    assign dBus_be    = (dBus_cmd_payload_size == 2'd0) ? (4'b0001 << dBus_cmd_payload_address[1:0]) : 
                        (dBus_cmd_payload_size == 2'd1) ? (4'b0011 << dBus_cmd_payload_address[1:0]) : 
                                                           4'b1111;

    //============================================================
    // CPU memory instruction read port
    //============================================================
    always @(posedge clk) begin
        iBus_rsp_valid  <= iBus_cmd_valid;
    end

    always @(posedge clk) begin 
        iBus_rsp_payload_error        <= (iBus_cmd_payload_pc[31:mem_addr_bits] != 0);

        iBus_rsp_payload_inst[ 7: 0]  <= mem0[iBus_cmd_payload_pc[mem_addr_bits-1:2]];
        iBus_rsp_payload_inst[15: 8]  <= mem1[iBus_cmd_payload_pc[mem_addr_bits-1:2]];
        iBus_rsp_payload_inst[23:16]  <= mem2[iBus_cmd_payload_pc[mem_addr_bits-1:2]];
        iBus_rsp_payload_inst[31:24]  <= mem3[iBus_cmd_payload_pc[mem_addr_bits-1:2]];
    end

    //============================================================
    // CPU memory data read/write port
    //============================================================
    reg [31:0] mem_rdata;

    wire [3:0] mem_wr;
    assign mem_wr = {4{dBus_cmd_valid && !dBus_cmd_payload_address[31] && dBus_cmd_payload_wr}} & dBus_be;

    // Quartus 13.0sp1 (the last version that supports Cyclone II) is
    // very picky about how RTL should structured to infer a true dual-ported RAM...
    always @(posedge clk) begin
        if (mem_wr[0]) begin
            mem0[dBus_cmd_payload_address[mem_addr_bits-1:2]]    <= dBus_wdata[ 7: 0];
            mem_rdata[ 7: 0]  <= dBus_wdata[ 7: 0];
        end
        else 
            mem_rdata[ 7: 0]  <= mem0[dBus_cmd_payload_address[mem_addr_bits-1:2]];

        if (mem_wr[1]) begin
            mem1[dBus_cmd_payload_address[mem_addr_bits-1:2]]    <= dBus_wdata[15: 8];
            mem_rdata[15: 8]  <= dBus_wdata[15: 8];
        end
        else 
            mem_rdata[15: 8]  <= mem1[dBus_cmd_payload_address[mem_addr_bits-1:2]];

        if (mem_wr[2]) begin
            mem2[dBus_cmd_payload_address[mem_addr_bits-1:2]]    <= dBus_wdata[23:16];
            mem_rdata[23:16]  <= dBus_wdata[23:16];
        end
        else 
            mem_rdata[23:16]  <= mem2[dBus_cmd_payload_address[mem_addr_bits-1:2]];

        if (mem_wr[3]) begin
            mem3[dBus_cmd_payload_address[mem_addr_bits-1:2]]    <= dBus_wdata[31:24];
            mem_rdata[31:24]  <= dBus_wdata[31:24];
        end
        else 
            mem_rdata[31:24]  <= mem3[dBus_cmd_payload_address[mem_addr_bits-1:2]];
    end

    //============================================================
    // Peripherals
    //============================================================

    reg [31:0] periph_rdata;
    reg led_access, status_access;

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            led0            <= 1'b1;
            led1            <= 1'b1;
            led2            <= 1'b1;
            periph_rdata    <= 32'd0;
            led_access      <= 1'b0;
            status_access   <= 1'b0;
        end
        else begin 
            led_access      <= 1'b0;
            status_access   <= 1'b0;

            if (dBus_cmd_valid && dBus_cmd_payload_address[31]) begin
    
                // LED register
                if (dBus_cmd_payload_address[mem_addr_bits-1:2] == 10'h0) begin
                    led_access      <= 1'b1;
                    if (dBus_cmd_payload_wr) begin
                        // LEDs are active low...
                        led0        <= !dBus_wdata[0];
                        led1        <= !dBus_wdata[1];
                        led2        <= !dBus_wdata[2];
    
                    end
                    else begin
                        periph_rdata        <= 'd0;
                        periph_rdata[0]     <= !led0;
                        periph_rdata[1]     <= !led1;
                        periph_rdata[2]     <= !led2;
                    end
                end
    
                // Status register
                if (dBus_cmd_payload_address[mem_addr_bits-1:2] == 10'h1) begin
                    status_access   <= 1'b1;

                    if (!dBus_cmd_payload_wr) begin
                        periph_rdata[0]     <= button_sync[1];
    
                        // I don't want to compile different 2 SW version for
                        // simulation and HW, so this status bit can be used by 
                        // the SW on which platform it's running.
`ifdef SIMULATION
                        periph_rdata[1]     <= 1'b1;
`else
                        periph_rdata[1]     <= 1'b0;
`endif
                    end
                end
            end
        end
    end

    reg [1:0] button_sync;

    always @(posedge clk) begin
        // double FF synchronizer
        button_sync <= { button_sync[0], button };
    end

    //============================================================
    // Merge read paths
    //============================================================

    reg periph_sel;
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            dBus_rsp_ready  <= 1'b0;
            periph_sel      <= 1'b0;
        end
        else begin
            // Both memory reads and peripheral reads don't support wait
            // cycles. Data is always returned immediately the next cycle.
            dBus_rsp_ready  <= dBus_cmd_valid && !dBus_cmd_payload_wr;
            periph_sel      <= dBus_cmd_payload_address[31];
        end
    end

    assign dBus_rsp_data = periph_sel ? periph_rdata : mem_rdata;

endmodule

