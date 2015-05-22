use std::collections::HashMap;
use std::ffi::CString;

use rustc::llvm::{self, ContextRef, ModuleRef, BuilderRef, BasicBlockRef, PassManagerRef,
                  TargetMachineRef};


pub struct Ctxt {
    pub context: Context,
    pub module: Module,
    pub builder: Builder,
    pub named_values: HashMap<String, ValueRef>
}

impl Ctxt {
    pub fn new(module_name: &str) -> Self {
        let context = Context::new();
        let module = context.module_create_with_name(module_name);
        let builder = context.create_builder();
        Ctxt {
            context: context,
            module: module,
            builder: builder,
            named_values: HashMap::new()
        }
    }
}

fn str_to_c_str(s: &str) -> *const i8 {
    let c_str = match CString::new(s) {
        Ok(c_str) => c_str,
        Err(e) => panic!("Error converting string '{}' to C string, null byte at position {}",
                         s, e.nul_position())
    };
    c_str.as_ptr()
}

// LLVM Wrappers

pub use rustc::llvm::{ValueRef, TypeRef, FileType, CodeGenModel, RelocMode, CodeGenOptLevel};

pub struct Context {
    pub context: ContextRef
}

impl Context {
    pub fn new() -> Self {
        let context = unsafe {
            llvm::LLVMContextCreate()
        };
        Context { context: context }
    }

    pub fn create_builder(&self) -> Builder {
        let builder = unsafe {
            llvm::LLVMCreateBuilderInContext(self.context)
        };
        Builder { builder: builder }
    }

    pub fn module_create_with_name(&self, name: &str) -> Module {
        let c_name = str_to_c_str(name);
        let module = unsafe {
            llvm::LLVMModuleCreateWithNameInContext(c_name, self.context)
        };
        Module { module: module }
    }

    pub fn int32_type(&self) -> TypeRef {
        unsafe {
            llvm::LLVMInt32TypeInContext(self.context)
        }
    }

    pub fn int16_type(&self) -> TypeRef {
        unsafe {
            llvm::LLVMInt16TypeInContext(self.context)
        }
    }

    pub fn int8_type(&self) -> TypeRef {
        unsafe {
            llvm::LLVMInt8TypeInContext(self.context)
        }
    }

    pub fn int1_type(&self) -> TypeRef {
        unsafe {
            llvm::LLVMInt1TypeInContext(self.context)
        }
    }

    pub fn const_bool(&self, val: bool) -> ValueRef {
        let ty = self.int1_type();
        const_int(ty, val as u64, false)
    }

    pub fn append_basic_block(&self, func: ValueRef, name: &str) -> BasicBlockRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMAppendBasicBlockInContext(self.context, func, c_name)
        }
    }
}

pub fn const_int(ty: TypeRef, val: u64, signed: bool) -> ValueRef {
    unsafe {
        llvm::LLVMConstInt(ty, val, signed as u32)
    }
}

impl Drop for Context {
    fn drop(&mut self) {
        unsafe {
            llvm::LLVMContextDispose(self.context);
        }
    }
}

pub struct Module {
    pub module: ModuleRef
}

impl Module {
    pub fn dump(&self) {
        unsafe {
            llvm::LLVMDumpModule(self.module)
        }
    }

    pub fn add_function(&self, func_ty: TypeRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMAddFunction(self.module, c_name, func_ty)
        }
    }

    pub fn get_named_function(&self, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMGetNamedFunction(self.module, c_name)
        }
    }
}

impl Drop for Module {
    fn drop(&mut self) {
        unsafe {
            llvm::LLVMDisposeModule(self.module);
        }
    }
}

pub struct Builder {
    pub builder: BuilderRef
}

impl Builder {
    pub fn position_at_end(&self, basic_block: BasicBlockRef) {
        unsafe {
            llvm::LLVMPositionBuilderAtEnd(self.builder, basic_block);
        }
    }

    pub fn build_ret(&self, ret_val: ValueRef) -> ValueRef {
        unsafe {
            llvm::LLVMBuildRet(self.builder, ret_val)
        }
    }

    pub fn build_alloca(&self, ty: TypeRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildAlloca(self.builder, ty, c_name)
        }
    }

    pub fn build_store(&self, val: ValueRef, ptr: ValueRef) -> ValueRef {
        unsafe {
            llvm::LLVMBuildStore(self.builder, val, ptr)
        }
    }

    pub fn build_load(&self, ptr: ValueRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildLoad(self.builder, ptr, c_name)
        }
    }

    pub fn build_call(&self, func: ValueRef, args: Vec<ValueRef>,
                      name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildCall(self.builder, func, args.as_ptr(), args.len() as u32, c_name)
        }
    }

    pub fn build_add(&self, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildAdd(self.builder, lhs, rhs, c_name)
        }
    }

    pub fn build_sub(&self, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildSub(self.builder, lhs, rhs, c_name)
        }
    }

    pub fn build_mul(&self, lhs: ValueRef, rhs: ValueRef, name: &str) -> ValueRef {
        let c_name = str_to_c_str(name);
        unsafe {
            llvm::LLVMBuildMul(self.builder, lhs, rhs, c_name)
        }
    }
}

impl Drop for Builder {
    fn drop(&mut self) {
        unsafe {
            llvm::LLVMDisposeBuilder(self.builder);
        }
    }
}

pub fn function_type(ret_ty: TypeRef, param_types: Vec<TypeRef>, is_var_args: bool) -> TypeRef {
    unsafe {
        llvm::LLVMFunctionType(ret_ty, param_types.as_ptr(), param_types.len() as u32,
                               is_var_args as u32)
    }
}

pub fn pointer_type(ty: TypeRef, address_space: u32) -> TypeRef {
    unsafe {
        llvm::LLVMPointerType(ty, address_space)
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

pub fn set_value_name(val: ValueRef, name: &str) {
    let c_name = str_to_c_str(name);
    unsafe {
        llvm::LLVMSetValueName(val, c_name);
    }
}

pub fn create_pass_manager() -> PassManagerRef {
    unsafe {
        llvm::LLVMCreatePassManager()
    }
}

pub fn rust_print_module(pm: PassManagerRef, module: ModuleRef, path: &str) {
    let c_path = str_to_c_str(path);
    unsafe {
        llvm::LLVMRustPrintModule(pm, module, c_path);
    }
}

pub fn rust_create_target_machine(triple: &str, cpu: &str, features: &str, model: CodeGenModel,
                                  reloc: RelocMode, level: CodeGenOptLevel, enable_segstk: bool,
                                  use_soft_fp: bool, no_frame_pointer_elim: bool, pie: bool,
                                  func_sections: bool, data_sections: bool) -> TargetMachineRef {
    let c_triple = str_to_c_str(triple);
    let c_cpu = str_to_c_str(cpu);
    let c_features = str_to_c_str(features);
    unsafe {
        llvm::LLVMRustCreateTargetMachine(c_triple, c_cpu, c_features, model, reloc, level,
                                          enable_segstk, use_soft_fp, no_frame_pointer_elim, pie,
                                          func_sections, data_sections)
    }
}

pub fn rust_write_output_file(target: TargetMachineRef, pm: PassManagerRef, module: Module,
                              path: &str, file_type: FileType) -> bool {
    let c_path = str_to_c_str(path);
    unsafe {
        llvm::LLVMRustWriteOutputFile(target, pm, module.module, c_path, file_type)
    }
}
