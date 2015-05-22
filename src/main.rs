#![feature(plugin, str_char, box_patterns, rustc_private, libc)]
#![plugin(peg_syntax_ext)]

extern crate rustc;
extern crate rustc_serialize;
extern crate libc;

mod llvm;

use lang::program;
use llvm::{ValueRef, TypeRef, Ctxt, FileType, CodeGenModel, RelocMode, CodeGenOptLevel};
use BinOp::{AddOp, SubOp, MulOp, DivOp};

use std::env;
use std::fs::File;
use std::io::Read;

peg_file! lang("grammar.rustpeg");

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
pub struct Program {
    fns: Vec<FnDecl>
}

impl Program {
    fn gen(&self, ctxt: &mut Ctxt) {
        for func in self.fns.iter() {
            func.gen(ctxt);
        }
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct FnDecl {
    ty: Type,
    name: String,
    args: ArgList,
    block: Block
}

impl FnDecl {
    fn gen(&self, ctxt: &mut Ctxt) {
        assert_eq!(ctxt.named_values.len(), 0);

        let ret_ty = self.ty.gen_type(ctxt);
        let param_types = self.args.gen_types(ctxt);
        let func_ty = llvm::function_type(ret_ty, param_types, false);
        let func = ctxt.module.add_function(func_ty, &self.name);

        let mut param = llvm::get_first_param(func);
        for var in self.args.args.iter() {
            ctxt.named_values.insert(var.name.clone(), param);
            llvm::set_value_name(param, &var.name);
            param = llvm::get_next_param(param);
        }

        let basic_block = ctxt.context.append_basic_block(func, "entry");
        ctxt.builder.position_at_end(basic_block);
        self.block.gen(ctxt);

        ctxt.named_values.clear();
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct ArgList {
    args: Vec<Variable>
}

impl ArgList {
    fn gen_types(&self, ctxt: &mut Ctxt) -> Vec<TypeRef> {
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
    UserTy(String)
}

impl Type {
    fn gen_type(&self, ctxt: &mut Ctxt) -> TypeRef {
        match self {
            &Type::IntTy => ctxt.context.int32_type(),
            &Type::StringTy => llvm::pointer_type(ctxt.context.int8_type(), 0),
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
                ctxt.builder.build_store(expr_res, ptr)
            }
            &Stmt::ExprStmt(ref e) => e.gen(ctxt),
            &Stmt::ReturnStmt(ref e) => {
                let expr_res = e.gen(ctxt);
                ctxt.builder.build_ret(expr_res)
            }
            &Stmt::AssignStmt(ref var_name, ref e) => {
                let val = ctxt.named_values.get(var_name).expect("Variable not found").clone();
                let expr_res = e.gen(ctxt);
                ctxt.builder.build_store(expr_res, val)
            }
        };
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
enum Expr {
    True,
    False,
    Num(i32),
    BinExpr(Box<Expr>, BinOp, Box<Expr>),
    EmptyExpr,
    IdentExpr(String),
    FuncCallExpr(String, Vec<Expr>)
}

impl Expr {
    fn gen(&self, ctxt: &mut Ctxt) -> ValueRef {
        match self {
            &Expr::True => ctxt.context.const_bool(true),
            &Expr::False => ctxt.context.const_bool(false),
            &Expr::Num(ref n) => {
                let ty = ctxt.context.int32_type();
                llvm::const_int(ty, *n as u64, false)
            }
            &Expr::BinExpr(ref l, op, ref r) => {
                let left = l.gen(ctxt);
                let right = r.gen(ctxt);
                match op {
                    AddOp => ctxt.builder.build_add(left, right, "addtmp"),
                    SubOp => ctxt.builder.build_sub(left, right, "subtmp"),
                    MulOp => ctxt.builder.build_mul(left, right, "multmp"),
                    DivOp => unimplemented!()
                }
            }
            &Expr::IdentExpr(ref name) => {
                let ptr = ctxt.named_values.get(name).expect("Variable not found").clone();
                ctxt.builder.build_load(ptr, name)
            },
            &Expr::FuncCallExpr(ref func_name, ref arg_exprs) => {
                let func = ctxt.module.get_named_function(func_name);
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

fn get_filename() -> Result<String, String> {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        Ok(args[1].clone())
    } else {
        Err(args[0].clone())
    }
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
    use std::ffi::CStr;
    let filename = match get_filename() {
        Ok(f) => f,
        Err(name) => { println!("Usage: {} filename", name); return }
    };
    let ast = construct_ast(&filename);
    let mut context = Ctxt::new("main");
    ast.gen(&mut context);
    unsafe {
        rustc::llvm::LLVMInitializeX86TargetInfo();
        rustc::llvm::LLVMInitializeX86Target();
        rustc::llvm::LLVMInitializeX86TargetMC();
    }

    let target = llvm::rust_create_target_machine("x86_64-unknown-linux-gnu", "native", "",
                                                  CodeGenModel::CodeModelDefault,
                                                  RelocMode::RelocDefault,
                                                  CodeGenOptLevel::CodeGenLevelNone, false, false,
                                                  false, false, false, false);

    let pm = llvm::create_pass_manager();
    llvm::rust_write_output_file(target, pm, context.module, "foo.out",
                                 FileType::AssemblyFileType);
    //context.module.dump();
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
