#![feature(plugin, str_char, box_patterns, rustc_private, libc)]
#![plugin(peg_syntax_ext)]

extern crate rustc;
extern crate rustc_serialize;
extern crate libc;

mod llvm;

use lang::program;
use llvm::{ValueRef, TypeRef, Context};
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
    fn gen(&self, context: &mut Context) {
        for func in self.fns.iter() {
            func.gen(context);
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
    fn gen(&self, context: &mut Context) {
        let ret_ty = self.ty.gen_type(context);
        let param_types = self.args.gen_types(context);
        let func_ty = llvm::function_type(ret_ty, param_types, false);
        let func = llvm::add_function(context.module, func_ty, &self.name);

        let mut param = llvm::get_first_param(func);
        for var in self.args.args.iter() {
            context.named_values.insert(var.name.clone(), param);
            llvm::set_value_name(param, &var.name);
            param = llvm::get_next_param(param);
        }

        let basic_block = llvm::append_basic_block_in_context(context.context, func, "entry");
        llvm::position_builder_at_end(context.builder, basic_block);
        self.block.gen(context);

        context.named_values.clear();
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct ArgList {
    args: Vec<Variable>
}

impl ArgList {
    fn gen_types(&self, context: &mut Context) -> Vec<TypeRef> {
        let mut types = Vec::with_capacity(self.args.len());
        for var in self.args.iter() {
            types.push(var.ty.gen_type(context));
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
    fn gen_type(&self, context: &mut Context) -> TypeRef {
        match self {
            &Type::IntTy => llvm::int32_type_in_context(context.context),
            &Type::StringTy => llvm::pointer_type(llvm::int8_type_in_context(context.context), 0),
            _ => unimplemented!()
        }
    }
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct Block {
    stmts: Vec<Stmt>
}

impl Block {
    fn gen(&self, context: &mut Context) {
        for stmt in self.stmts.iter() {
            stmt.gen(context);
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
    fn gen(&self, context: &mut Context) {
        match self {
            &Stmt::DeclStmt(ref var, ref e) => {
                let ptr = llvm::build_alloca(context.builder, var.ty.gen_type(context), &var.name);
                context.named_values.insert(var.name.clone(), ptr);
                llvm::build_store(context.builder, e.gen(context), ptr)
            }
            &Stmt::ExprStmt(ref e) => e.gen(context),
            &Stmt::ReturnStmt(ref e) => llvm::build_ret(context.builder, e.gen(context)),
            &Stmt::AssignStmt(ref var_name, ref e) => {
                let val = context.named_values.get(var_name).expect("Variable not found").clone();
                llvm::build_store(context.builder, e.gen(context), val)
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
    fn gen(&self, context: &mut Context) -> ValueRef {
        match self {
            &Expr::True => llvm::const_bool(context.context, true),
            &Expr::False => llvm::const_bool(context.context, false),
            &Expr::Num(ref n) => {
                let ty = llvm::int32_type_in_context(context.context);
                llvm::const_int(ty, *n as u64, false)
            }
            &Expr::BinExpr(ref l, op, ref r) => {
                let left = l.gen(context);
                let right = r.gen(context);
                match op {
                    AddOp => llvm::build_add(context.builder, left, right, "addtmp"),
                    SubOp => llvm::build_sub(context.builder, left, right, "subtmp"),
                    MulOp => llvm::build_mul(context.builder, left, right, "multmp"),
                    DivOp => unimplemented!()
                }
            }
            &Expr::IdentExpr(ref name) => {
                let ptr = context.named_values.get(name).expect("Variable not found").clone();
                llvm::build_load(context.builder, ptr, name)
            },
            &Expr::FuncCallExpr(ref func_name, ref arg_exprs) => {
                let func = llvm::get_named_function(context.module, func_name);
                let args: Vec<_> = arg_exprs.iter().map(|e| e.gen(context)).collect();
                llvm::build_call(context.builder, func, args, func_name)
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
    let filename = match get_filename() {
        Ok(f) => f,
        Err(name) => { println!("Usage: {} filename", name); return }
    };
    let ast = construct_ast(&filename);
    let mut context = Context::new("main");
    ast.gen(&mut context);
    llvm::dump_module(context.module);
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
