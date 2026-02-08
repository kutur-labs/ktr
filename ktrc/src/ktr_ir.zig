//! Public module root for the ktr intermediate representation.
//!
//! Downstream packages (e.g. ktrr) depend on this module to access
//! IR types and the `.ktrir` text parser.

const ir = @import("ir.zig");
const ir_parse = @import("ir_parse.zig");

pub const Ir = ir.Ir;
pub const Input = ir.Input;
pub const Inst = ir.Inst;
pub const Value = ir.Value;
pub const Type = ir.Type;
pub const Op = ir.Op;
pub const Operand = ir.Operand;
pub const LengthUnit = @import("unit.zig").LengthUnit;
pub const parse = ir_parse.parse;
pub const ParseError = ir_parse.Error;
pub const isTemp = ir.isTemp;
pub const formatF64 = ir.formatF64;
