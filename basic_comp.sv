module basic_comp (
	clk,
	set_S, set_FGI, set_FGO,
	FGI_out, FGO_out,
	INPR_in, OUTR_out
);
		
	input clk;
	input [7:0] INPR_in;
	input set_S, set_FGI, set_FGO;
	output reg[7:0] OUTR_out;
	output reg FGI_out,FGO_out;
	
	
	wire [11:0] PC_in, PC_out, AR_in, AR_out;
	wire [15:0] IR_in, IR_out, TR_in, TR_out, DR_in, AC_in, DR_out, AC_out ;
	wire [7:0] OUTR_in, INPR_out;
	wire load_PC, load_AR, load_IR, load_TR, load_DR, load_AC, load_INPR, load_OUTR;
	wire clr_PC, clr_AR, clr_AC;
	wire inc_PC, inc_AR, inc_DR, inc_AC;
	reg E;
	wire carry_in;
	wire [2:0] bus_select;
	wire IRQ_in, IRQ_out, set_IRQ, clr_IRQ;
	wire IEN_in, IEN_out, set_IEN, clr_IEN;
	wire FGI_in, clr_FGI;
	wire FGO_in, clr_FGO;
	wire S_in, S_out, clr_S;
	wire AC_zero, DR_zero;
	wire RAM_r,RAM_w;
	wire [15:0] ram_in,ram_out;
	reg [15:0] bus_in [0:7];
	wire [15:0] bus_out;
	reg AC_MSB;
	
	
	assign AC_MSB = AC_out[15];
	assign AC_zero = ~(|AC_out);
	assign DR_zero = ~(|DR_out);
	assign bus_in[0] = 0;
	assign bus_in[1] = AR_out;
	assign bus_in[2] = PC_out;
	assign bus_in[3] = DR_out;
	assign bus_in[4] = AC_out;
	assign bus_in[5] = IR_out;
	assign bus_in[6] = TR_out;
	assign bus_in[7] = ram_out;
	assign ram_in = bus_out;
	
	register #(12) PC(clk, bus_out, PC_out, load_PC, clr_PC, inc_PC);
	register #(12) AR(clk, bus_out, AR_out, load_AR, clr_AR, inc_AR);
	register #(16) IR(clk, bus_out, IR_out, load_IR, 1'b0, 1'b0);
	register #(16) TR(clk, bus_out, TR_out, load_TR, 1'b0, 1'b0);
	register #(16) DR(clk, bus_out, DR_out, load_DR, 1'b0, inc_DR);
	register #(16) AC(clk, AC_in, AC_out, load_AC, clr_AC, inc_AC);
	register #(8) INPR(clk, INPR_in, INPR_out, load_INPR, 1'b0, 1'b0);
	register #(8) OUTR(clk, bus_out, OUTR_out, load_OUTR, 1'b0, 1'b0);
	
	ff E_ff(clk, carry_in, E, load_E, 1'b0, clr_E, comp_E);
	
	ff IRQ_ff(clk, IRQ_in, IRQ_out, 1'b0, set_IRQ, clr_IRQ, 1'b0);
	
	ff IEN_ff(clk, IEN_in, IEN_out, 1'b0, set_IEN, clr_IEN, 1'b0);
	
	ff FGI_ff(clk, FGI_in, FGI_out, 1'b0, set_FGI, clr_FGI, 1'b0);
	
	ff FGO_ff(clk, FGO_in, FGO_out, 1'b0, set_FGO, clr_FGO, 1'b0);
	
	ff S_ff(clk, S_in, S_out, 1'b0, set_S, clr_S, 1'b0);
	
	control_timing_unit u1(
	// Inputs
	.clk(clk), .IR(IR_out),
	.IRQ(IRQ_out), .IEN(IEN_out), .FGI(FGI_out), .FGO(FGO_out), .E(E), 
	.AC_MSB(AC_MSB),
	.AC_zero(AC_zero), 
	.DR_zero(DR_zero),

	// Outputs
	.load_AR(load_AR), .clr_AR(clr_AR), .inc_AR(inc_AR),
	.load_PC(load_PC), .clr_PC(clr_PC), .inc_PC(inc_PC),
	.load_DR(load_DR), .inc_DR(inc_DR),
	.load_AC(load_AC), .clr_AC(clr_AC), .inc_AC(inc_AC),
	.load_IR(load_IR),
	.load_TR(load_TR),
	.load_OUTR(load_OUTR),
	.set_IRQ(set_IRQ), .clr_IRQ(clr_IRQ),
	.set_IEN(set_IEN), .clr_IEN(clr_IEN),
	.load_E(load_E), .clr_E(clr_E), .comp_E(comp_E),
	.clr_S(clr_S),
	.clr_FGI(clr_FGI),
	.clr_FGO(clr_FGO),
	.ALU_and(ALU_and), .ALU_add(ALU_add), .ALU_comp(ALU_comp), .ALU_cir(ALU_cir), 
	.ALU_cil(ALU_cil), .ALU_trans_dr(ALU_trans_dr), .ALU_trans_inpr(ALU_trans_inpr),
	.RAM_r(RAM_r), .RAM_w(RAM_w),
	.bus_select(bus_select)
);

	alu u2(
	// Inputs
	.from_DR(DR_out), .from_INPR(INPR_out), .from_AC(AC_out), .from_E(E),
	// Outputs
	.out(AC_in), .carry(carry_in),
	// Signals
	.and_(ALU_and), .add(ALU_add), .comp(ALU_comp), .cir(ALU_cir), .cil(ALU_cil), 
	.trans_dr(ALU_trans_dr), .trans_inpr(ALU_trans_inpr)
);

	bus #(16,3) u3(
	.select(bus_select),
	.in(bus_in), .out(bus_out)
);

	ram #(12,16) u4(
	.clk(clk),
	.addr(AR_out),
	.r(RAM_r), .w(RAM_w),
	.in(ram_in), .out(ram_out)
);

endmodule


/*
 * CPU modules
 */
module control_timing_unit (
	// Inputs
	clk, IR,
	IRQ, IEN, FGI, FGO, E, AC_MSB, AC_zero, DR_zero,

	// Outputs
	load_AR, clr_AR, inc_AR,
	load_PC, clr_PC, inc_PC,
	load_DR, inc_DR,
	load_AC, clr_AC, inc_AC,
	load_IR,
	load_TR,
	load_OUTR,
	set_IRQ, clr_IRQ,
	set_IEN, clr_IEN,
	load_E, clr_E, comp_E,
	clr_S,
	clr_FGI,
	clr_FGO,
	ALU_and, ALU_add, ALU_comp, ALU_cir, ALU_cil, ALU_trans_dr, ALU_trans_inpr,
	RAM_r, RAM_w,
	bus_select
);

	/* FILL HERE */
	input clk, IRQ, IEN, FGI, FGO, E, AC_MSB, AC_zero, DR_zero;
	input [15:0] IR;
	output reg load_AR, clr_AR, inc_AR,
	load_PC, clr_PC, inc_PC,
	load_DR, inc_DR,
	load_AC, clr_AC, inc_AC,
	load_IR,
	load_TR,
	load_OUTR,
	set_IRQ, clr_IRQ,
	set_IEN, clr_IEN,
	load_E, clr_E, comp_E,
	clr_S,
	clr_FGI,
	clr_FGO,
	ALU_and, ALU_add, ALU_comp, ALU_cir, ALU_cil, ALU_trans_dr, ALU_trans_inpr,
	RAM_r, RAM_w;
	output reg [2:0] bus_select;
	
	reg [7:0] D;
	reg [3:0] SC_out;
	reg [15:0] T;
	reg I;
	wire load_I;
	wire clr_SC;
	
	control_logic u1(//Inputs
	.clk(clk), .D(D), .T(T),
	.IR(IR), .I(I), .IRQ(IRQ), .IEN(IEN), .FGI(FGI), .FGO(FGO),
	.E(E), .AC_MSB(AC_MSB), .AC_zero(AC_zero), .DR_zero(DR_zero),
	// Outputs
	.load_AR(load_AR), .clr_AR(clr_AR), .inc_AR(inc_AR),
	.load_PC(load_PC), .clr_PC(clr_PC), .inc_PC(inc_PC),
	.load_DR(load_DR), .inc_DR(inc_DR),
	.load_AC(load_AC), .clr_AC(clr_AC), .inc_AC(inc_AC),
	.load_IR(load_IR),
	.load_TR(load_TR),
	.load_OUTR(load_OUTR),
	.load_I(load_I),
	.set_IRQ(set_IRQ), .clr_IRQ(clr_IRQ),
	.set_IEN(set_IEN), .clr_IEN(clr_IEN),
	.load_E(load_E), .clr_E(clr_E), .comp_E(comp_E),
	.clr_S(clr_S),
	.clr_FGI(clr_FGI),
	.clr_FGO(clr_FGO),
	.clr_SC(clr_SC),
	.ALU_and(ALU_and), .ALU_add(ALU_add), .ALU_comp(ALU_comp),
	.ALU_cir(ALU_cir), .ALU_cil(ALU_cil), .ALU_trans_dr(ALU_trans_dr),
	.ALU_trans_inpr(ALU_trans_inpr),
	.RAM_r(RAM_r), .RAM_w(RAM_w),
	.bus_select(bus_select));
	
	decoder #(3) dec3_8(IR[14:12],D);
	
	counter seq_counter(clk,SC_out,clr_SC);
	
	decoder #(4) dec4_16(SC_out,T);
	
	ff I_ff(clk, IR[15], I, load_I, 1'b0, 1'b0, 1'b0);
	
	

endmodule


module control_logic (
	// Inputs
	clk, D, T,
	IR, I, IRQ, IEN, FGI, FGO, E, AC_MSB, AC_zero, DR_zero,
	// Outputs
	load_AR, clr_AR, inc_AR,
	load_PC, clr_PC, inc_PC,
	load_DR, inc_DR,
	load_AC, clr_AC, inc_AC,
	load_IR,
	load_TR,
	load_OUTR,
	load_I,
	set_IRQ, clr_IRQ,
	set_IEN, clr_IEN,
	load_E, clr_E, comp_E,
	clr_S,
	clr_FGI,
	clr_FGO,
	clr_SC,
	ALU_and, ALU_add, ALU_comp, ALU_cir, ALU_cil, ALU_trans_dr, ALU_trans_inpr,
	RAM_r, RAM_w,
	bus_select
);

	input clk, I, IRQ, IEN, FGI, FGO, E, AC_MSB, AC_zero, DR_zero;
	input [15:0] IR;
	input [7:0] D;
	input [15:0] T;
	output reg load_AR, clr_AR, inc_AR,
	load_PC, clr_PC, inc_PC,
	load_DR, inc_DR,
	load_AC, clr_AC, inc_AC,
	load_IR,
	load_TR,
	load_OUTR,
	load_I,
	set_IRQ, clr_IRQ,
	set_IEN, clr_IEN,
	load_E, clr_E, comp_E,
	clr_S,
	clr_FGI,
	clr_FGO,
	clr_SC,
	ALU_and, ALU_add, ALU_comp, ALU_cir, ALU_cil, ALU_trans_dr, ALU_trans_inpr,
	RAM_r, RAM_w;
	output reg [2:0] bus_select;
	
	wire r, p;
	reg[11:0] B;
	reg [7:0] x;
	
	assign B = IR[11:0];
	assign r = D[7] & ~I & T[3];
	assign p = D[7] & I & T[3];
	assign ALU_and = D[0]&T[5];
	assign ALU_add = D[1]&T[5];
	assign ALU_cir = r & B[7];
	assign ALU_cil = r & B[6];
	assign ALU_trans_dr = D[2] & T[5];
	assign ALU_trans_inpr = p & B[11];
	assign ALU_comp = r & B[9];
	assign RAM_r = ~IRQ & T[1] | ~D[7] & I & T[3] | (D[0]|D[1]|D[2]|D[6])&T[4];
	assign RAM_w = IRQ & T[1] | (D[3]|D[5])&T[4] | D[6]&T[6];
	assign clr_SC = IRQ & T[2] | (D[0]|D[1]|D[2]|D[5])&T[5] | (D[3]|D[4])&T[4] | D[6]&T[6] | r | p;
	assign clr_FGO = p & B[10];
	assign clr_FGI = p & B[11];
	assign clr_S = r & B[0];
	assign clr_E = r & B[10];
	assign comp_E = r & B[8];
	assign load_E = r & (B[7]|B[6]) | D[1] & T[5];
	assign set_IEN = p & B[7];
	assign clr_IEN = IRQ & T[2] | p & B[6];
	assign clr_IRQ = IRQ & T[2];
	assign set_IRQ = ~T[0] & ~T[1] & ~T[2] & IEN & (FGI | FGO);
	assign load_I = ~IRQ & T[2];
	assign load_OUTR = p & B[10];
	assign load_TR = IRQ & T[0];
	assign load_IR = ~IRQ & T[1];
	assign load_AC = (D[0]|D[1]|D[2]) & T[5] | r & (B[6]|B[7]|B[9])|p&B[11];
	assign clr_AC = r & B[11];
	assign inc_AC = r & B[5];
	assign load_DR = (D[0]|D[1]|D[2] | D[6]) & T[4]; 
	assign inc_DR = D[6] & T[5];
	assign load_PC = D[4]&T[4] | D[5] & T[5];
	assign inc_PC = ~IRQ & T[1] | IRQ & T[2] | D[6] & T[6] & DR_zero | 
	r & B[1] & E | r & B[2] & AC_zero | r & B[3] & AC_MSB | r & B[4] & ~AC_MSB 
	| p & (B[8] | B[9]);
	assign clr_PC = IRQ & T[1];
	assign load_AR = ~IRQ & (T[0]|T[2]) | ~D[7] & I & T[3];
	assign clr_AR = IRQ & T[0];
	assign inc_AR = D[5] & T[4];
	assign x[0] = 1'b0;
	assign x[1] = D[4] & T[4] | D[5] & T[5];
	assign x[2] = ~IRQ & T[0] | IRQ & T[0] | D[5] & T[4] ;
	assign x[3] = D[2] & T[5] | D[6] & T[6];
	assign x[4] = D[3] & T[4] | p & IR[10];
	assign x[5] = ~IRQ & T[2];
	assign x[6] = IRQ & T[1];
	assign x[7] = ~IRQ & T[1] | ~D[7] & I & T[3] | (D[0]|D[1]|D[2]|D[6])&T[4];
	encoder #(3) enc8_3(x,bus_select);
	
endmodule


module alu (
	// Inputs
	from_DR, from_INPR, from_AC, from_E,
	// Outputs
	out, carry,
	// Signals
	and_, add, comp, cir, cil, trans_dr, trans_inpr
);

	/* FILL HERE */
	input [15:0] from_DR;
	input [7:0] from_INPR;
	input [15:0] from_AC;
	input from_E;
	input and_, add, comp, cir, cil, trans_dr, trans_inpr;
	output reg[15:0] out;
	output reg carry;
	
	initial begin
	out = 16'b0;
	end
	
	always @(*)
	begin
			if(and_) out <= from_AC & from_DR;
			else if(add) {carry, out} <= from_AC + from_DR;
			else if(comp) out <= ~from_AC;
			else if(cir) 
			begin
				out <= {from_E,from_AC[15:1]};
				carry <= from_AC[0];
			end
			else if(cil) 
			begin
				out <= {from_AC[14:0],from_E};
				carry <= from_AC[15];
			end
			else if(trans_dr) out <= from_DR;
			else if(trans_inpr) out <= from_INPR;	
	end
endmodule


/*
 * Basic modules
 */
 module register #(parameter WIDTH = 8) (
	clk,
	in, out,
	load, clr, inc
);
 	input clk;
	input [WIDTH-1:0] in;
	output reg [WIDTH-1:0] out;
	input load, clr, inc;

	initial
	begin
		out = {WIDTH{1'b0}};
	end

	always @(posedge clk)
	begin
		if (load)
			out <= in;
		else if (clr)
			out <= {WIDTH{1'b0}};
		else if (inc)
			out <= out + {{WIDTH-1{1'b0}}, 1'b1};
	end
endmodule


module ff (
	clk,
	in, out,
	load, set, clr, comp
);
	input clk;
	input in;
	output reg out;
	input load, set, clr, comp;

	initial
	begin
		out = 1'b0;
	end

	always @(posedge clk)
	begin
		if (load)
			out <= in;
		else if (set)
			out <= 1'b1;
		else if (clr)
			out <= 1'b0;
		else if (comp)
			out <= ~out;
	end
endmodule


module counter #(parameter WIDTH = 4) (
	clk,
	out,
	clr,
);
	input clk;
	output reg [WIDTH-1:0] out;
	input clr;

	initial
	begin
		out = {WIDTH{1'b0}};
	end

	always @(posedge clk)
	begin
		if (clr)
			out <= {WIDTH{1'b0}};
		else
			out <= out + {{WIDTH-1{1'b0}}, 1'b1};
	end
endmodule


module decoder #(parameter IN_WIDTH = 3) (
	in, out
);
	input [IN_WIDTH-1:0] in;
	output reg [(1<<IN_WIDTH)-1:0] out;

	always @(in)
	begin
		out = {(1<<IN_WIDTH){1'b0}};
		out[in] = 1'b1;
	end

endmodule


module encoder #(parameter OUT_WIDTH = 3) (
	in,	out
);
	input [(1<<OUT_WIDTH)-1:0] in;
	output reg [OUT_WIDTH-1:0] out;

	integer i;
	always @(in)
	begin
		out = {OUT_WIDTH{1'b0}};
		for (i=(1<<OUT_WIDTH)-1; i>=0; i=i-1)
			if (in[i]) out = i;
	end
endmodule


module bus #(parameter DATA_WIDTH = 16, SELECT_WIDTH = 3) (
	select,
	in, out
);
	input [SELECT_WIDTH-1:0] select;
	input [DATA_WIDTH-1:0] in [0:(1<<SELECT_WIDTH)-1];
	output reg [DATA_WIDTH-1:0] out;

	always @(*)
	begin
		out = in[select];
	end
endmodule


module ram #(parameter ADDR_WIDTH = 12, DATA_WIDTH = 16) (
	clk,
	addr,
	r, w,
	in, out
);
	input clk;
	input [ADDR_WIDTH-1:0] addr;
	input r;
	input w;
	input [DATA_WIDTH-1:0] in;
	output [DATA_WIDTH-1:0] out;

	reg [DATA_WIDTH-1:0] memory [0:(1<<ADDR_WIDTH)-1];
	
	initial begin							

	$readmemh("test.txt",memory,0,4095);

	end
	
	
	assign out = r ? memory[addr] : {DATA_WIDTH{1'bz}};

	always @(posedge clk)
		if (w)
			memory[addr] <= in;

endmodule






module testbench();

reg clk = 1'b0;
reg [7:0] INPR_in;
reg set_S, set_FGI, set_FGO;
reg [7:0] OUTR_out;
reg FGI_out,FGO_out;

basic_comp DUT(clk,INPR_in,set_S, set_FGI, set_FGO,OUTR_out, FGI_out,FGO_out);


initial
begin

set_S = 1'b1; 
set_FGI=1'b0;
set_FGO=1'b0;

end

always     // no sensitivity list, so it always executes 

	begin 
		clk = 1; #5; clk = 0; #5;
	end
	
endmodule
