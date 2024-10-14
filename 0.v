// Benchmark "exact" written by ABC on Mon Oct 14 12:05:09 2024

module exact ( 
    a, b, c, d,
    e  );
  input  a, b, c, d;
  output e;
  wire new_n6, new_n7;
  assign new_n6 = ~a & b;
  assign new_n7 = a & ~c;
  assign e = new_n6 & new_n7;
endmodule


