#![feature(plugin, str_char, box_patterns)]
#![plugin(peg_syntax_ext)]

extern crate rustc_serialize;

use lang::program;

use std::env;
use std::fs::File;
use std::io::Read;

peg_file! lang("grammar.rustpeg");

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
pub struct Program {
    fns: Vec<FnDecl>
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct FnDecl {
    ty: Type,
    name: String,
    args: ArgList,
    block: Block
}

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct ArgList {
    args: Vec<Variable>
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

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
struct Block {
    stmts: Vec<Stmt>
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

#[derive(Debug, Eq, PartialEq, RustcDecodable, RustcEncodable)]
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
    println!("{:?}", construct_ast(&filename));
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
