#![feature(plugin, str_char, box_patterns)]
#![plugin(peg_syntax_ext)]

extern crate llvm_sys;
extern crate getopts;
extern crate rustc_serialize;
extern crate env_logger;

#[macro_use]
extern crate log;

mod llvm;

use llvm_sys::LLVMIntPredicate::*;
use llvm::Ctxt;
use lang::program;
use llvm_sys::prelude::*;
use llvm_sys::target_machine::*;
use BinOp::{AddOp, SubOp, MulOp, DivOp, LessOp, GreaterOp, EqualsOp};

use getopts::Options;

use std::env;
use std::fs::File;
use std::io::Read;
use std::path::Path;

peg_file! lang("grammar.rustpeg");

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
pub struct Program {
    extern_decls: Vec<ExternDecl>,
    fns: Vec<Function>
}

impl Program {
    fn gen(&self, ctxt: &mut Ctxt) {
        for decl in self.extern_decls.iter() {
            decl.gen(ctxt);
        }
        ctxt.named_values.clear();

        for func in self.fns.iter() {
            func.gen(ctxt);
        }
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct ExternDecl {
    decl: FnDecl
}

impl ExternDecl {
    fn gen(&self, ctxt: &mut Ctxt) {
        self.decl.gen(ctxt);
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct FnDecl {
    ty: Type,
    name: String,
    args: ArgList
}

impl FnDecl {
    fn gen(&self, ctxt: &mut Ctxt) -> LLVMValueRef {
        let ret_ty = self.ty.gen_type(ctxt);
        let param_types = self.args.gen_types(ctxt);
        let func_ty = llvm::function_type(ret_ty, param_types, false);
        let func = ctxt.module.add_function(func_ty, &self.name);

        let mut param = llvm::get_first_param(func);
        for var in self.args.args.iter() {
            let param_ = param.unwrap();
            ctxt.named_values.insert(var.name.clone(), param_);
            llvm::set_value_name(param_, &var.name);
            param = llvm::get_next_param(param_);
        }

        func
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct Function {
    decl: FnDecl,
    block: Block
}

impl Function {
    fn gen(&self, ctxt: &mut Ctxt) {
        assert_eq!(ctxt.named_values.len(), 0);

        let func = self.decl.gen(ctxt);
        assert_eq!(ctxt.cur_func, None);
        ctxt.cur_func = Some(func);

        let basic_block = ctxt.context.append_basic_block(func, "entry");
        ctxt.builder.position_at_end(basic_block);
        self.block.gen(ctxt);

        if self.decl.ty == Type::VoidTy {
            ctxt.builder.build_ret_void();
        }

        ctxt.named_values.clear();
        ctxt.cur_func = None;
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct ArgList {
    args: Vec<Variable>
}

impl ArgList {
    fn gen_types(&self, ctxt: &mut Ctxt) -> Vec<LLVMTypeRef> {
        let mut types = Vec::with_capacity(self.args.len());
        for var in self.args.iter() {
            types.push(var.ty.gen_type(ctxt));
        }
        types
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct Variable {
    ty: Type,
    name: String
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum Type {
    IntTy,
    StringTy,
    VoidTy,
    BoolTy,
    UserTy(String)
}

impl Type {
    fn gen_type(&self, ctxt: &mut Ctxt) -> LLVMTypeRef {
        match self {
            &Type::IntTy => ctxt.context.int32_type(),
            &Type::StringTy => llvm::pointer_type(ctxt.context.int8_type(), 0),
            &Type::VoidTy => ctxt.context.void_type(),
            &Type::BoolTy => ctxt.context.int1_type(),
            _ => unimplemented!()
        }
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct Block {
    stmts: Vec<Stmt>
}

impl Block {
    fn gen(&self, ctxt: &mut Ctxt) {
        for stmt in self.stmts.iter() {
            stmt.gen(ctxt);
        }
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum Stmt {
    DeclStmt(Variable, Expr),
    ExprStmt(Expr),
    ReturnStmt(Expr),
    AssignStmt(String, Expr),
    IfStmt(Expr, Block, Option<Block>),
    WhileStmt(Expr, Block)
}

impl Stmt {
    fn gen(&self, ctxt: &mut Ctxt) {
        match self {
            &Stmt::DeclStmt(ref var, ref e) => {
                let ty = var.ty.gen_type(ctxt);
                let ptr = ctxt.builder.build_alloca(ty, &var.name);
                ctxt.named_values.insert(var.name.clone(), ptr);
                let expr_res = e.gen(ctxt);
                ctxt.builder.build_store(expr_res, ptr);
            }
            &Stmt::ExprStmt(ref e) => { e.gen(ctxt); },
            &Stmt::ReturnStmt(ref e) => {
                let expr_res = e.gen(ctxt);
                ctxt.builder.build_ret(expr_res);
            }
            &Stmt::AssignStmt(ref var_name, ref e) => {
                let val = ctxt.named_values.get(var_name).expect("Variable not found").clone();
                let expr_res = e.gen(ctxt);
                ctxt.builder.build_store(expr_res, val);
            }
            &Stmt::IfStmt(ref cond, ref then_block, ref maybe_else_block) => {
                let func = ctxt.cur_func.unwrap(); // TODO
                let cond_res = cond.gen(ctxt);
                let then_bb = ctxt.context.append_basic_block(func, "if.then");
                let maybe_else_bb = if maybe_else_block.is_some() {
                    Some(ctxt.context.append_basic_block(func, "if.else"))
                } else {
                    None
                };
                let end_bb = ctxt.context.append_basic_block(func, "if.end");

                if let (&Some(ref else_block), Some(else_bb)) = (maybe_else_block, maybe_else_bb) {
                    ctxt.builder.build_cond_br(cond_res, then_bb, else_bb);
                    ctxt.builder.position_at_end(else_bb);
                    else_block.gen(ctxt);
                    ctxt.builder.build_br(end_bb);
                } else {
                    ctxt.builder.build_cond_br(cond_res, then_bb, end_bb);
                }

                ctxt.builder.position_at_end(then_bb);
                then_block.gen(ctxt);
                ctxt.builder.build_br(end_bb);

                ctxt.builder.position_at_end(end_bb);
            }
            _ => unimplemented!()
        };
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum Expr {
    LitExpr(Literal),
    BinExpr(Box<Expr>, BinOp, Box<Expr>),
    EmptyExpr,
    IdentExpr(String),
    FuncCallExpr(String, Vec<Expr>)
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum Literal {
    NumLit(i32),
    BoolLit(bool),
    StrLit(String)
}

impl Literal {
    fn gen(&self, ctxt: &mut Ctxt) -> LLVMValueRef {
        match self {
            &Literal::BoolLit(b) => ctxt.context.const_bool(b),
            &Literal::NumLit(ref n) => {
                let ty = ctxt.context.int32_type();
                llvm::const_int(ty, *n as u64, false)
            }
            &Literal::StrLit(ref s) => {
                let i32_ty = ctxt.context.int32_type();
                let indices = vec![llvm::const_int(i32_ty, 0, false),
                                   llvm::const_int(i32_ty, 0, false)];
                let ptr = ctxt.builder.build_global_string(s, "str");
                // TODO: What is the name argument for?
                ctxt.builder.build_in_bounds_gep(ptr, indices, "str")
            }
        }
    }
}

impl Expr {
    fn gen(&self, ctxt: &mut Ctxt) -> LLVMValueRef {
        match self {
            &Expr::LitExpr(ref lit) => lit.gen(ctxt),
            &Expr::BinExpr(ref l, op, ref r) => {
                let left = l.gen(ctxt);
                let right = r.gen(ctxt);
                match op {
                    AddOp => ctxt.builder.build_add(left, right, "addtmp"),
                    SubOp => ctxt.builder.build_sub(left, right, "subtmp"),
                    MulOp => ctxt.builder.build_mul(left, right, "multmp"),
                    DivOp => ctxt.builder.build_sdiv(left, right, "sdivtmp"),
                    LessOp => ctxt.builder.build_icmp(LLVMIntSLT, left, right, "slt"),
                    GreaterOp => ctxt.builder.build_icmp(LLVMIntSGT, left, right, "sgt"),
                    EqualsOp => ctxt.builder.build_icmp(LLVMIntEQ, left, right, "eq")
                }
            }
            &Expr::IdentExpr(ref name) => {
                let ptr = ctxt.named_values.get(name).expect("Variable not found").clone();
                ctxt.builder.build_load(ptr, name)
            },
            &Expr::FuncCallExpr(ref func_name, ref arg_exprs) => {
                let func = ctxt.module.get_named_function(func_name).unwrap();
                let args: Vec<_> = arg_exprs.iter().map(|e| e.gen(ctxt)).collect();
                ctxt.builder.build_call(func, args, func_name)
            }
            _ => unimplemented!()
        }
    }
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum BinOp {
    AddOp,
    SubOp,
    MulOp,
    DivOp,
    LessOp,
    GreaterOp,
    EqualsOp
}

#[derive(Debug, Eq, PartialEq)]
enum OutputType {
    AST,
    LLVM,
    Assembly,
    Object
}

#[derive(Debug)]
struct Config {
    input_filename: String,
    output_filename: Option<String>,
    output_type: OutputType,
}

impl Config {
    fn new(in_file: String, out_file: Option<String>, type_: OutputType) -> Self {
        Config { input_filename: in_file, output_filename: out_file, output_type: type_ }
    }
}

fn parse_options() -> Option<Config> {
    fn print_usage(program: &str, opts: Options) {
        print!("{}", opts.usage(&format!("Usage: {} [options]", program)));
    }

    let mut opts = Options::new();
    opts.optflag("h", "help", "print this help menu");
    opts.optopt("t", "type", "output type (llvm (default), asm, or obj)", "TYPE");
    opts.optopt("o", "output", "output file name", "FILE");
    let args: Vec<_> = env::args().collect();

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => panic!("{}", e)
    };

    if matches.opt_present("h") {
        print_usage(&args[0], opts);
        return None;
    }

    let input_filename = if !matches.free.is_empty() {
        matches.free[0].clone()
    } else {
        print_usage(&args[0], opts);
        return None;
    };

    let output_type = if matches.opt_present("t") {
        let type_name = matches.opt_str("t").unwrap();
        match &*type_name {
            "ast" => OutputType::AST,
            "llvm" => OutputType::LLVM,
            "asm" => OutputType::Assembly,
            "obj" => OutputType::Object,
            _ => panic!("Invalid output type '{}'", type_name)
        }
    } else {
        OutputType::LLVM
    };


    let output_filename = if output_type != OutputType::AST {
        if matches.opt_present("o") {
            Some(matches.opt_str("o").unwrap())
        } else {
            let mut base = Path::new(&input_filename).file_stem().unwrap()
                .to_str().unwrap().to_owned();
            match output_type {
                OutputType::LLVM => base.push_str(".ll"),
                OutputType::Assembly => base.push_str(".s"),
                OutputType::Object => base.push_str(".o"),
                _ => unreachable!()
            }
            Some(base)
        }
    } else {
        None
    };

    Some(Config::new(input_filename, output_filename, output_type))
}

fn construct_ast(filename: &str) -> Program {
    let mut f = match File::open(filename) {
        Ok(f) => f,
        Err(e) => panic!(e)
    };

    let mut code = String::new();
    f.read_to_string(&mut code).ok().expect("Error reading from file");
    match program(&code) {
        Ok(p) => p,
        Err(e) => panic!("{}", e)
    }
}

fn main() {
    env_logger::init().unwrap();
    let config = match parse_options() {
        Some(config) => config,
        None => return
    };
    debug!("Configuration: {:?}", config);

    let ast = construct_ast(&config.input_filename);
    let mut context = Ctxt::new("main");


    if config.output_type == OutputType::AST {
        println!("{:?}", ast)
    } else if config.output_type == OutputType::LLVM {
        ast.gen(&mut context);
        llvm::print_module_to_file(&context.module,
                                   config.output_filename.as_ref().unwrap()).unwrap();
        // TODO: stdout: println!("{}", llvm::print_module_to_string(&context.module));
    } else {
        ast.gen(&mut context);
        let file_type = match config.output_type {
            OutputType::Assembly => LLVMCodeGenFileType::LLVMAssemblyFile,
            OutputType::Object => LLVMCodeGenFileType::LLVMObjectFile,
            _ => unreachable!()
        };

        llvm::initialize_native_target();
        llvm::initialize_native_asm_printer();

        let target = llvm::get_target_from_name("x86-64").unwrap();
        let triple = llvm::get_default_target_triple();
        let tm = llvm::create_target_machine(target, triple, "", "",
                                             LLVMCodeGenOptLevel::LLVMCodeGenLevelNone,
                                             LLVMRelocMode::LLVMRelocDefault,
                                             LLVMCodeModel::LLVMCodeModelDefault);
        llvm::target_machine_emit_to_file(tm, &mut context.module,
                                          config.output_filename.as_ref().unwrap(),
                                          file_type).unwrap()
    }
}

#[cfg(test)]
mod test {
    extern crate rustc_serialize;

    use lang::program;

    use std::fs::File;
    use std::io::Read;

    use rustc_serialize::json;

    #[test]
    fn test() {
        let mut code = String::new();
        let mut f = File::open("tests/test.lang").unwrap();
        f.read_to_string(&mut code).ok().expect("Unable to read code file");
        program(&code).unwrap();
    }
}
