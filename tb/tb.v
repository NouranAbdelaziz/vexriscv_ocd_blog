`default_nettype none
`timescale 1ns/100ps

module tb;

    reg clk = 0;

    always begin
        clk=0;
        #50;
        clk=1;
        #50;
    end

    reg rstn;
    // RESET
    initial begin
        clk = 0;
        rstn = 1;
        #10;
        @(posedge clk);
        rstn = 0;
        #100;
        @(posedge clk);
        rstn = 1;
    end

    initial begin
        if ($test$plusargs("fst"))
            $dumpfile("waves.fst");
        else
            $dumpfile("waves.vcd");
        $dumpvars();
        repeat(1000) @(posedge clk);
        $finish;
    end

    wire led0, led1, led2, button;

    /*top u_top(
        .clk(clk),
        .jtag_tck(1'b0),
        .jtag_tms(1'b0),
        .jtag_tdi(1'b0),
        .led0(led0),
        .led1(led1),
        .led2(led2),
        .button(button)
    );*/

    top u_top(
        .clk(clk),
        //.rstn(rstn),
        .led0(led0),
        .led1(led1),
        .led2(led2),
        .button(button),
        .uart_RX(1'b0),
        .uart_TX()
    );
    
    reg led0_d, led1_d, led2_d;

    always @(posedge clk) begin
        if (led0 != led0_d) begin
            $display("%d: led0 changed to %d", $time, led0);
        end
        if (led1 != led1_d) begin
            $display("%d: led1 changed to %d", $time, led1);
        end
        if (led2 != led2_d) begin
            $display("%d: led2 changed to %d", $time, led2);
        end

        led0_d <= led0;
        led1_d <= led1;
        led2_d <= led2;
    end

endmodule
