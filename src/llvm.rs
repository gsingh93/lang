use std::collections::HashMap;
use std::ffi::CString;

use rustc::llvm::{self, ContextRef, ModuleRef, BuilderRef, BasicBlockRef};

pub struct Context {
    pub module: ModuleRef,
    pub context: ContextRef,
    pub builder: BuilderRef,
    pub named_values: HashMap<String, ValueRef>
}

impl Context {
    pub fn new(module_name: &str) -> Self {
        let c_module_name = CString::new(module_name).unwrap();
        unsafe {
            let context = llvm::LLVMContextCreate();
            Context {
                context: context,
                module: llvm::LLVMModuleCreateWithNameInContext(c_module_name.as_ptr(), context),
                builder: llvm::LLVMCreateBuilderInContext(context),
                named_values: HashMap::new()
            }
        }
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            llvm::LLVMDisposeBuilder(self.builder);
            llvm::LLVMDisposeModule(self.module);
            llvm::LLVMContextDispose(self.context);
        }
    }
}

// LLVM Wrappers

pub use rustc::llvm::{ValueRef, TypeRef};

pub fn dump_module(module: ModuleRef) {
    unsafe {
        llvm::LLVMDumpModule(module)
    }
}

pub fn function_type(ret_ty: TypeRef, param_types: Vec<TypeRef>, is_var_args: bool) -> TypeRef {
    unsafe {
        llvm::LLVMFunctionType(ret_ty, param_types.as_ptr(), param_types.len() as u32,
                               is_var_args as u32)
    }
}

pub fn add_function(module: ModuleRef, func_ty: TypeRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMAddFunction(module, c_name.as_ptr(), func_ty)
    }
}

pub fn get_first_param(func: ValueRef) -> ValueRef {
    unsafe {
        llvm::LLVMGetFirstParam(func)
    }
}

pub fn get_next_param(param: ValueRef) -> ValueRef {
    unsafe {
        llvm::LLVMGetNextParam(param)
    }
}

pub fn pointer_type(ty: TypeRef, address_space: u32) -> TypeRef {
    unsafe {
        llvm::LLVMPointerType(ty, address_space)
    }
}

pub fn int32_type_in_context(context: ContextRef) -> TypeRef {
    unsafe {
        llvm::LLVMInt32TypeInContext(context)
    }
}

pub fn int16_type_in_context(context: ContextRef) -> TypeRef {
    unsafe {
        llvm::LLVMInt16TypeInContext(context)
    }
}

pub fn int8_type_in_context(context: ContextRef) -> TypeRef {
    unsafe {
        llvm::LLVMInt8TypeInContext(context)
    }
}

pub fn int1_type_in_context(context: ContextRef) -> TypeRef {
    unsafe {
        llvm::LLVMInt1TypeInContext(context)
    }
}

pub fn const_int(ty: TypeRef, val: u64, signed: bool) -> ValueRef {
    unsafe {
        llvm::LLVMConstInt(ty, val, signed as u32)
    }
}

pub fn const_bool(context: ContextRef, val: bool) -> ValueRef {
    let ty = int1_type_in_context(context);
    const_int(ty, val as u64, false)
}

pub fn build_add(builder: BuilderRef, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildAdd(builder, lhs, rhs, c_name.as_ptr())
    }
}

pub fn build_sub(builder: BuilderRef, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildSub(builder, lhs, rhs, c_name.as_ptr())
    }
}

pub fn build_mul(builder: BuilderRef, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildMul(builder, lhs, rhs, c_name.as_ptr())
    }
}

pub fn set_value_name(val: ValueRef, name: &str) {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMSetValueName(val, c_name.as_ptr());
    }
}

pub fn append_basic_block_in_context(context: ContextRef, func: ValueRef,
                                     name: &str) -> BasicBlockRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMAppendBasicBlockInContext(context, func, c_name.as_ptr())
    }
}

pub fn position_builder_at_end(builder: BuilderRef, basic_block: BasicBlockRef) {
    unsafe {
        llvm::LLVMPositionBuilderAtEnd(builder, basic_block);
    }
}

pub fn build_ret(builder: BuilderRef, ret_val: ValueRef) -> ValueRef {
    unsafe {
        llvm::LLVMBuildRet(builder, ret_val)
    }
}

pub fn build_alloca(builder: BuilderRef, ty: TypeRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildAlloca(builder, ty, c_name.as_ptr())
    }
}

pub fn build_store(builder: BuilderRef, val: ValueRef, ptr: ValueRef) -> ValueRef {
    unsafe {
        llvm::LLVMBuildStore(builder, val, ptr)
    }
}

pub fn build_load(builder: BuilderRef, ptr: ValueRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildLoad(builder, ptr, c_name.as_ptr())
    }
}

pub fn get_named_function(module: ModuleRef, name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMGetNamedFunction(module, c_name.as_ptr())
    }
}

pub fn build_call(builder: BuilderRef, func: ValueRef, args: Vec<ValueRef>,
                  name: &str) -> ValueRef {
    let c_name = CString::new(name).unwrap();
    unsafe {
        llvm::LLVMBuildCall(builder, func, args.as_ptr(), args.len() as u32, c_name.as_ptr())
    }
}
