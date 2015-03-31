#![feature(plugin, collections, str_char, box_patterns)]
#![plugin(peg_syntax_ext)]

use lang::program;

use std::env;
use std::fs::File;
use std::io::Read;

peg_file! lang("grammar.rustpeg");

#[derive(Debug, Eq, PartialEq)]
pub struct Program {
    fns: Vec<FnDecl>
}

#[derive(Debug, Eq, PartialEq)]
struct FnDecl {
    ty: String,
    name: String,
    block: Block
}

#[derive(Debug, Eq, PartialEq)]
struct Block {
    stmts: Vec<Stmt>
}

#[derive(Debug, Eq, PartialEq)]
enum Stmt {
    DeclStmt(String, String, Expr),
    ExprStmt(Expr),
    ReturnStmt(Expr),
    AssignStmt(String, Expr)
}

#[derive(Debug, Eq, PartialEq)]
enum Expr {
    True,
    False,
    Num(i32),
    BinExpr(Box<Expr>, BinOp, Box<Expr>),
    EmptyExpr
}

#[derive(Debug, Eq, PartialEq)]
enum BinOp {
    AddOp,
    SubOp,
    MulOp,
    DivOp
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
    println!("{:?}", construct_ast(&filename));
}

#[test]
fn test() {
    let ast = construct_ast("tests/test.lang");
    println!("{:?}", ast);
}
