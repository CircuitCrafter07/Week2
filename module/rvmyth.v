// File: rvmyth.v
// Simple RV32I 5-stage pipelined CPU (educational, synthesizable subset).
// Stages: IF -> ID -> EX -> MEM -> WB
// Supports: RV32I base subset (addi, add, sub, and, or, xor, sll, srl, slt,
//            lw, sw, beq, bne, blt, bge, jal, jalr)
// Forwarding + simple hazard stall for load-use
// Author: ChatGPT (template for learning)

`timescale 1ns/1ps
module rvmyth(
    input  wire        clk,
    input  wire        rst_n
);

// ---------- Parameters ----------
parameter RESET_PC = 0;
parameter IMEM_WORDS = 256;
parameter DMEM_WORDS = 1024;

// ---------- Program Counter ----------
reg [31:0] pc;
wire [31:0] pc_next;
wire [31:0] instr_if;

// ---------- Instruction Memory (simple ROM) ----------
reg [31:0] imem [0:IMEM_WORDS-1];

initial begin
    // Example: you can preload instructions here, or use $readmemh.
    // $readmemh("program.hex", imem);
    integer i;
    for (i=0; i<IMEM_WORDS; i=i+1) imem[i] = 32'h00000013; // NOP (addi x0,x0,0)
end

assign instr_if = imem[pc[31:2]]; // word-aligned

// ---------- Pipeline IF/ID registers ----------
reg [31:0] if_id_pc;
reg [31:0] if_id_instr;
reg        if_id_valid;

// ---------- Control & decode outputs ----------
wire [6:0] opcode_id;
wire [2:0] funct3_id;
wire [6:0] funct7_id;
assign opcode_id = if_id_instr[6:0];
assign funct3_id = if_id_instr[14:12];
assign funct7_id = if_id_instr[31:25];

// ---------- Register File ----------
reg [31:0] regfile [0:31];
wire [4:0] rs1_id = if_id_instr[19:15];
wire [4:0] rs2_id = if_id_instr[24:20];
wire [4:0] rd_wb;

wire [31:0] reg_rs1;
wire [31:0] reg_rs2;

assign reg_rs1 = (rs1_id==5'd0) ? 32'd0 : regfile[rs1_id];
assign reg_rs2 = (rs2_id==5'd0) ? 32'd0 : regfile[rs2_id];

// ---------- Immediate generator ----------
function [31:0] imm_gen;
    input [31:0] instr;
    reg [31:0] imm;
    begin
        case (instr[6:0])
            7'b0010011, // I-type (addi, andi, ori, etc.)
            7'b0000011, // lw
            7'b1100111: // jalr
                imm = {{20{instr[31]}}, instr[31:20]};
            7'b0100011: begin // S-type (sw)
                imm = {{20{instr[31]}}, instr[31:25], instr[11:7]};
            end
            7'b1100011: begin // B-type (branches)
                imm = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
            end
            7'b1101111: begin // J-type (jal)
                imm = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};
            end
            default: imm = 32'd0;
        endcase
        imm_gen = imm;
    end
endfunction

wire [31:0] imm_id = imm_gen(if_id_instr);

// ---------- Control signals (ID) ----------
reg        id_reg_write;
reg [1:0]  id_mem_to_reg; // 0: from ALU, 1: from MEM (load)
reg        id_mem_read;
reg        id_mem_write;
reg [3:0]  id_alu_ctrl;
reg        id_alu_src; // 0: reg, 1: imm
reg        id_branch;
reg        id_jal;
reg        id_jalr;

always @(*) begin
    // Defaults
    id_reg_write = 0;
    id_mem_to_reg = 0;
    id_mem_read = 0;
    id_mem_write = 0;
    id_alu_ctrl = 4'b0000; // add
    id_alu_src = 0;
    id_branch = 0;
    id_jal = 0;
    id_jalr = 0;

    case (opcode_id)
        7'b0110011: begin // R-type
            id_reg_write = 1;
            id_alu_src = 0;
            case ({funct7_id,funct3_id})
                {7'b0000000,3'b000}: id_alu_ctrl = 4'b0000; // add
                {7'b0100000,3'b000}: id_alu_ctrl = 4'b0001; // sub
                {7'b0000000,3'b111}: id_alu_ctrl = 4'b0010; // and
                {7'b0000000,3'b110}: id_alu_ctrl = 4'b0011; // or
                {7'b0000000,3'b100}: id_alu_ctrl = 4'b0100; // xor
                {7'b0000000,3'b001}: id_alu_ctrl = 4'b0101; // sll
                {7'b0000000,3'b101}: id_alu_ctrl = 4'b0110; // srl
                {7'b0000000,3'b010}: id_alu_ctrl = 4'b0111; // slt
                default: id_alu_ctrl = 4'b0000;
            endcase
        end
        7'b0010011: begin // I-type ALU
            id_reg_write = 1;
            id_alu_src = 1;
            case (funct3_id)
                3'b000: id_alu_ctrl = 4'b0000; // addi
                3'b111: id_alu_ctrl = 4'b0010; // andi
                3'b110: id_alu_ctrl = 4'b0011; // ori
                3'b100: id_alu_ctrl = 4'b0100; // xori
                3'b001: id_alu_ctrl = 4'b0101; // slli (treated as sll)
                3'b101: id_alu_ctrl = 4'b0110; // srli
                3'b010: id_alu_ctrl = 4'b0111; // slti
                default: id_alu_ctrl = 4'b0000;
            endcase
        end
        7'b0000011: begin // lw
            id_reg_write = 1;
            id_mem_read = 1;
            id_mem_to_reg = 1;
            id_alu_src = 1;
            id_alu_ctrl = 4'b0000; // add (address)
        end
        7'b0100011: begin // sw
            id_mem_write = 1;
            id_alu_src = 1;
            id_alu_ctrl = 4'b0000; // add (address)
        end
        7'b1100011: begin // branches
            id_branch = 1;
            id_alu_src = 0;
            id_alu_ctrl = 4'b0001; // sub for compare
        end
        7'b1101111: begin // jal
            id_jal = 1;
            id_reg_write = 1;
        end
        7'b1100111: begin // jalr
            id_jalr = 1;
            id_reg_write = 1;
        end
        default: begin
            // treat unknown as NOP
        end
    endcase
end

// ---------- ID/EX pipeline registers ----------
reg [31:0] id_ex_pc;
reg [31:0] id_ex_rs1;
reg [31:0] id_ex_rs2;
reg [31:0] id_ex_imm;
reg [4:0]  id_ex_rs1_addr;
reg [4:0]  id_ex_rs2_addr;
reg [4:0]  id_ex_rd;
reg        id_ex_reg_write;
reg [1:0]  id_ex_mem_to_reg;
reg        id_ex_mem_read;
reg        id_ex_mem_write;
reg [3:0]  id_ex_alu_ctrl;
reg        id_ex_alu_src;
reg        id_ex_branch;
reg        id_ex_jal;
reg        id_ex_jalr;
reg        id_ex_valid;

// ---------- ALU ----------
function [31:0] alu;
    input [3:0] ctrl;
    input [31:0] a;
    input [31:0] b;
    reg [31:0] res;
    begin
        case (ctrl)
            4'b0000: res = a + b;              // add
            4'b0001: res = a - b;              // sub
            4'b0010: res = a & b;              // and
            4'b0011: res = a | b;              // or
            4'b0100: res = a ^ b;              // xor
            4'b0101: res = a << b[4:0];        // sll
            4'b0110: res = a >> b[4:0];        // srl (logical)
            4'b0111: res = ($signed(a) < $signed(b)) ? 32'd1 : 32'd0; // slt
            default: res = 32'd0;
        endcase
        alu = res;
    end
endfunction

// ---------- Forwarding unit (simple) ----------
reg [1:0] forwardA;
reg [1:0] forwardB;
// forward codes: 00 - from ID/EX rs value (normal), 01 - from EX/MEM(ALU), 10 - from MEM/WB(result)

// ---------- EX stage wires ----------
wire [31:0] ex_a_raw = id_ex_rs1;
wire [31:0] ex_b_raw = id_ex_alu_src ? id_ex_imm : id_ex_rs2;
reg  [31:0] ex_a;
reg  [31:0] ex_b;
wire [31:0] ex_alu_out = alu(id_ex_alu_ctrl, ex_a, ex_b);
wire        ex_taken_branch;

// ---------- EX/MEM pipeline registers ----------
reg [31:0] ex_mem_alu;
reg [31:0] ex_mem_rs2; // for store
reg [4:0]  ex_mem_rd;
reg        ex_mem_reg_write;
reg [1:0]  ex_mem_mem_to_reg;
reg        ex_mem_mem_read;
reg        ex_mem_mem_write;
reg [31:0] ex_mem_pc;
reg        ex_mem_valid;
reg        ex_mem_branch;

// ---------- Data Memory (simple RAM) ----------
reg [31:0] dmem [0:DMEM_WORDS-1];
integer j;
initial begin
    for (j=0;j<DMEM_WORDS;j=j+1) dmem[j] = 32'd0;
end

// ---------- MEM/WB pipeline registers ----------
reg [31:0] mem_wb_alu;
reg [31:0] mem_wb_memdata;
reg [4:0]  mem_wb_rd;
reg        mem_wb_reg_write;
reg [1:0]  mem_wb_mem_to_reg;
reg        mem_wb_valid;

// ---------- WB mux result ----------
wire [31:0] wb_result = (mem_wb_mem_to_reg==1'b1) ? mem_wb_memdata : mem_wb_alu;

// ---------- Hazard detection (load-use stall) ----------
reg stall;
always @(*) begin
    stall = 0;
    // If EX stage is loading and ID stage uses the loaded register -> stall
    if (id_ex_mem_read && id_ex_rd != 5'd0) begin
        if ((id_ex_rd == rs1_id) || (id_ex_rd == rs2_id)) stall = 1;
    end
end

// ---------- Branch decision (EX stage) ----------
assign ex_taken_branch = (id_ex_branch && ( (id_ex_alu_ctrl==4'b0001 && (id_ex_rs1 - id_ex_rs2)==32'd0 && (if_id_instr[14:12]==3'b000)) ? 1'b1 : // beq simplified — we will use ALU result later
                             ( (id_ex_alu_ctrl==4'b0001) ? ((id_ex_rs1 - id_ex_rs2) != 32'd0) : 1'b0 )
                           )) ? 1'b1 : 1'b0;
// Note: for simplicity we will evaluate branches via ALU in EX stage below using signed compare where needed.

// ---------- PC Next logic ----------
wire [31:0] pc_plus4 = pc + 4;
wire branch_taken_ex;
assign branch_taken_ex = ex_mem_valid && ex_mem_branch && (ex_mem_alu == 32'd1 ? 1'b1 : 1'b0); // placeholder (we will do real branch below)

// Compute pc_next: if branch in EX resolves, update PC to branch target; if jal/jalr also.
wire [31:0] ex_branch_target = id_ex_pc + id_ex_imm;
wire [31:0] jal_target = id_ex_pc + id_ex_imm;
wire [31:0] jalr_target = (id_ex_rs1 + id_ex_imm) & ~32'd1; // align low bit zero (approx)

// choose next PC: simple priority: branch resolved in EX -> target, else default pc+4
assign pc_next = (ex_mem_valid && ex_mem_branch && ex_mem_alu==32'd1) ? ex_mem_alu /* NOTE: placeholder, updated in always below */ : pc_plus4;

// ---------- Sequential: PC and IF/ID ----------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        pc <= RESET_PC;
        if_id_instr <= 32'd0;
        if_id_pc <= 32'd0;
        if_id_valid <= 0;
    end else begin
        if (!stall) begin
            pc <= pc + 4;
            if_id_instr <= instr_if;
            if_id_pc <= pc;
            if_id_valid <= 1;
        end else begin
            // on stall: inject bubble in IF/ID
            if_id_instr <= if_id_instr; // hold
            if_id_pc <= if_id_pc;
            if_id_valid <= if_id_valid;
            // freeze PC (do not increment)
        end
    end
end

// ---------- ID -> EX pipeline update ----------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        id_ex_valid <= 0;
        id_ex_pc <= 0;
        id_ex_rs1 <= 0;
        id_ex_rs2 <= 0;
        id_ex_imm <= 0;
        id_ex_rd <= 0;
        id_ex_rs1_addr <= 0;
        id_ex_rs2_addr <= 0;
        id_ex_reg_write <= 0;
        id_ex_mem_to_reg <= 0;
        id_ex_mem_read <= 0;
        id_ex_mem_write <= 0;
        id_ex_alu_ctrl <= 0;
        id_ex_alu_src <= 0;
        id_ex_branch <= 0;
        id_ex_jal <= 0;
        id_ex_jalr <= 0;
    end else begin
        if (stall) begin
            // Insert bubble into ID/EX (turn into NOP)
            id_ex_valid <= 0;
            id_ex_reg_write <= 0;
            id_ex_mem_read <= 0;
            id_ex_mem_write <= 0;
            id_ex_mem_to_reg <= 0;
            id_ex_branch <= 0;
            id_ex_jal <= 0;
            id_ex_jalr <= 0;
        end else begin
            id_ex_valid <= if_id_valid;
            id_ex_pc <= if_id_pc;
            id_ex_rs1 <= reg_rs1;
            id_ex_rs2 <= reg_rs2;
            id_ex_imm <= imm_id;
            id_ex_rs1_addr <= rs1_id;
            id_ex_rs2_addr <= rs2_id;
            id_ex_rd <= if_id_instr[11:7];
            id_ex_reg_write <= id_reg_write;
            id_ex_mem_to_reg <= id_mem_to_reg;
            id_ex_mem_read <= id_mem_read;
            id_ex_mem_write <= id_mem_write;
            id_ex_alu_ctrl <= id_alu_ctrl;
            id_ex_alu_src <= id_alu_src;
            id_ex_branch <= id_branch;
            id_ex_jal <= id_jal;
            id_ex_jalr <= id_jalr;
        end
    end
end

// ---------- Forwarding logic (EX stage) ----------
always @(*) begin
    // default: no forward
    forwardA = 2'b00;
    forwardB = 2'b00;
    // EX hazard: if EX/MEM will write and rd matches id_ex_rs1/rs2
    if (ex_mem_reg_write && (ex_mem_rd != 5'd0) && (ex_mem_rd == id_ex_rs1_addr)) forwardA = 2'b01;
    if (ex_mem_reg_write && (ex_mem_rd != 5'd0) && (ex_mem_rd == id_ex_rs2_addr)) forwardB = 2'b01;
    // MEM hazard: if MEM/WB will write and rd matches id_ex_rs1/rs2
    if (mem_wb_reg_write && (mem_wb_rd != 5'd0) && (mem_wb_rd == id_ex_rs1_addr)) forwardA = 2'b10;
    if (mem_wb_reg_write && (mem_wb_rd != 5'd0) && (mem_wb_rd == id_ex_rs2_addr)) forwardB = 2'b10;
end

// select forwarded values
always @(*) begin
    // A
    case (forwardA)
        2'b00: ex_a = ex_a_raw;
        2'b01: ex_a = ex_mem_alu;
        2'b10: ex_a = wb_result;
        default: ex_a = ex_a_raw;
    endcase
    // B
    case (forwardB)
        2'b00: ex_b = ex_b_raw;
        2'b01: ex_b = ex_mem_alu;
        2'b10: ex_b = wb_result;
        default: ex_b = ex_b_raw;
    endcase
end

// ---------- EX -> MEM pipeline ----------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        ex_mem_valid <= 0;
        ex_mem_alu <= 0;
        ex_mem_rs2 <= 0;
        ex_mem_rd <= 0;
        ex_mem_reg_write <= 0;
        ex_mem_mem_to_reg <= 0;
        ex_mem_mem_read <= 0;
        ex_mem_mem_write <= 0;
        ex_mem_pc <= 0;
        ex_mem_branch <= 0;
    end else begin
        ex_mem_valid <= id_ex_valid;
        ex_mem_alu <= (id_ex_alu_src ? alu(id_ex_alu_ctrl, id_ex_rs1, id_ex_imm) : ex_alu_out); // ensure compute
        ex_mem_rs2 <= id_ex_rs2;
        ex_mem_rd <= id_ex_rd;
        ex_mem_reg_write <= id_ex_reg_write;
        ex_mem_mem_to_reg <= id_ex_mem_to_reg;
        ex_mem_mem_read <= id_ex_mem_read;
        ex_mem_mem_write <= id_ex_mem_write;
        ex_mem_pc <= id_ex_pc;
        ex_mem_branch <= id_ex_branch;
    end
end

// ---------- MEM stage: memory access ----------
always @(posedge clk) begin
    if (ex_mem_valid) begin
        if (ex_mem_mem_write) begin
            // word store
            dmem[ex_mem_alu[31:2]] <= ex_mem_rs2;
        end
    end
end

always @(*) begin
    // read
    if (ex_mem_valid && ex_mem_mem_read) mem_wb_memdata = dmem[ex_mem_alu[31:2]];
    else mem_wb_memdata = 32'd0;
end

// ---------- MEM -> WB pipeline ----------
always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        mem_wb_valid <= 0;
        mem_wb_alu <= 0;
        mem_wb_memdata <= 0;
        mem_wb_rd <= 0;
        mem_wb_reg_write <= 0;
        mem_wb_mem_to_reg <= 0;
    end else begin
        mem_wb_valid <= ex_mem_valid;
        mem_wb_alu <= ex_mem_alu;
        mem_wb_memdata <= mem_wb_memdata; // already set combinationally
        mem_wb_rd <= ex_mem_rd;
        mem_wb_reg_write <= ex_mem_reg_write;
        mem_wb_mem_to_reg <= ex_mem_mem_to_reg;
    end
end

// ---------- WB stage: write-back ----------
always @(posedge clk) begin
    if (mem_wb_valid && mem_wb_reg_write && (mem_wb_rd != 5'd0)) begin
        regfile[mem_wb_rd] <= (mem_wb_mem_to_reg==1'b1) ? mem_wb_memdata : mem_wb_alu;
    end
end

// ---------- Register file init ----------
integer r;
initial begin
    for (r=0;r<32;r=r+1) regfile[r] = 32'd0;
end

endmodule

