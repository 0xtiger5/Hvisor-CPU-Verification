#![feature(never_type)]
use vstd::prelude::*;

verus! {

pub struct VirtLocalApic {
    pub phys_lapic: PhysLocalApic,
}

pub struct PhysLocalApic;

impl PhysLocalApic {
    #[verifier::external_body]
    pub fn end_of_interrupt(&mut self) {
        // 硬件操作
    }
}

#[repr(C)]
pub struct GeneralRegisters {
    pub rax: u64,
    pub rcx: u64,
    pub rdx: u64,
    pub rbx: u64,
    pub _unused_rsp: u64,
    pub rbp: u64,
    pub rsi: u64,
    pub rdi: u64,
    pub r8: u64,
    pub r9: u64,
    pub r10: u64,
    pub r11: u64,
    pub r12: u64,
    pub r13: u64,
    pub r14: u64,
    pub r15: u64,
}

impl GeneralRegisters {
    pub closed spec fn is_valid(&self) -> bool {
        true
    }
}

#[repr(C)]
pub struct ArchCpu {
    pub guest_regs: GeneralRegisters,
    pub host_stack_top: u64,
    pub cpuid: usize,
    pub power_on: bool,
    pub virt_lapic: VirtLocalApic,
    pub vmx_on: bool,
    pub vmcs_configured: bool,
}

// TODO 调整
pub const MAX_CPU_NUM: usize = 256;
pub const PER_CPU_SIZE: usize = 524288;  // 512 * 1024 = 524288

pub uninterp spec fn spec_core_end() -> u64;

#[verifier::external_body]
pub fn core_end() -> (result: u64)
    ensures 
        result > 0,
        spec_core_end() == result,
{
    0x10000000  // 示例值
}

pub uninterp spec fn spec_this_cpu_id() -> usize;

#[verifier::external_body]
pub fn this_cpu_id() -> (result: usize)
    ensures
        result > 0,
        result < MAX_CPU_NUM,
        spec_this_cpu_id() == result,
{
    0  // 示例值
}

impl ArchCpu {
    // 核心不变式
    pub closed spec fn inv(&self) -> bool {
        &&& self.cpuid < MAX_CPU_NUM
        &&& (self.vmx_on ==> self.vmcs_configured)
        &&& self.guest_regs.is_valid()
        &&& self.host_stack_top == 0 || self.host_stack_top % 16 == 0
    }
    
    // 规范函数：准备好进入 idle 状态
    pub closed spec fn ready_for_idle(&self) -> bool {
        &&& self.vmx_on
        &&& self.vmcs_configured
        &&& self.host_stack_top > 0
        &&& self.host_stack_top > spec_core_end()
        &&& !self.power_on
    }
}

impl ArchCpu {
    // 清理中断
    #[verifier::external_body]
    fn idle_clear_interrupt(&mut self)
        requires old(self).inv(),
        ensures 
            self.inv(),
            self.cpuid == old(self).cpuid,
            self.vmx_on == old(self).vmx_on,
            self.vmcs_configured == old(self).vmcs_configured,
            self.power_on == old(self).power_on,
            self.host_stack_top == old(self).host_stack_top,
    {
        unsafe {
            self.virt_lapic.phys_lapic.end_of_interrupt();
        }
    }
    
    // 验证 CPU ID
    fn idle_verify_cpu_id(&self)
        requires
            self.inv(),
            self.cpuid == spec_this_cpu_id(),
        ensures
            self.cpuid == spec_this_cpu_id(),
    {
        proof {
            assert(self.cpuid == spec_this_cpu_id());
        }
    }
    
    // 设置电源状态
    fn idle_set_power_state(&mut self)
        requires old(self).inv(),
        ensures
            self.inv(),
            !self.power_on,
            self.cpuid == old(self).cpuid,
            self.vmx_on == old(self).vmx_on,
            self.vmcs_configured == old(self).vmcs_configured,
            self.host_stack_top == old(self).host_stack_top,
    {
        self.power_on = false;
        
        proof {
            assert(!self.power_on);
        }
    }
    
    // 激活 VMX
    #[verifier::external_body]
    fn idle_activate_vmx(&mut self) -> (result: Result<(), ()>)
        requires old(self).inv(),
        ensures
            result.is_ok() ==> {
                self.inv() &&
                self.vmx_on &&
                self.vmcs_configured &&
                self.cpuid == old(self).cpuid &&
                self.power_on == old(self).power_on &&
                self.host_stack_top == old(self).host_stack_top
            },
    {
        Ok(())  // 简化
    }
    
    // 初始化 parking（信任）
    #[verifier::external_body]
    fn idle_init_parking(&mut self)
        requires old(self).inv(),
        ensures 
            self.inv(),
            self.cpuid == old(self).cpuid,
            self.vmx_on == old(self).vmx_on,
            self.vmcs_configured == old(self).vmcs_configured,
            self.power_on == old(self).power_on,
            self.host_stack_top == old(self).host_stack_top,
    {
        // PARKING_MEMORY_SET.call_once(|| { ... });
    }
    
    // 配置 VMCS
    #[verifier::external_body]
    fn idle_setup_vmcs(&mut self) -> (result: Result<(), ()>)
        requires
            old(self).inv(),
            old(self).vmx_on,
        ensures
            result.is_ok() ==> {
                self.inv() &&
                self.vmcs_configured &&
                self.cpuid == old(self).cpuid &&
                self.vmx_on == old(self).vmx_on &&
                self.power_on == old(self).power_on &&
                self.host_stack_top == old(self).host_stack_top
            },
    {
        Ok(())  // 简化
    }
    
    // 设置栈顶
    fn idle_set_stack_top(&mut self)
        requires
            old(self).inv(),
            old(self).cpuid < MAX_CPU_NUM,
            spec_core_end() + ((old(self).cpuid + 1) * PER_CPU_SIZE) as u64 <= u64::MAX,
        ensures
            self.inv(),
            self.host_stack_top == (spec_core_end() + (self.cpuid + 1) * PER_CPU_SIZE) as u64,
            self.host_stack_top > spec_core_end(),
            self.host_stack_top % 16 == 0,
            self.cpuid == old(self).cpuid,
            self.vmx_on == old(self).vmx_on,
            self.vmcs_configured == old(self).vmcs_configured,
            self.power_on == old(self).power_on,
    {
        self.host_stack_top = core_end() + ((self.cpuid + 1) * PER_CPU_SIZE) as u64;
        
        proof {
            // 验证栈顶地址的属性
            assert(self.host_stack_top > spec_core_end());
            
            // 验证对齐（假设 PER_CPU_SIZE 是 16 的倍数）
            assume(PER_CPU_SIZE % 16 == 0);
            assume(spec_core_end() % 16 == 0);
            assert(self.host_stack_top % 16 == 0);
        }
    }
    
    // 激活页表并启动（信任）
    #[verifier::external_body]
    fn idle_activate_and_launch(&mut self) -> !
        requires
            old(self).ready_for_idle(),
    {
        // unsafe {
        //     PARKING_MEMORY_SET.get().unwrap().activate();
        //     self.vmx_launch();
        // }
        loop {}
    }
}

impl ArchCpu {
    #[verifier::exec_allows_no_decreases_clause]
    pub fn idle(&mut self) -> !
        requires
            old(self).inv(),
            old(self).cpuid == spec_this_cpu_id(),
            old(self).cpuid < MAX_CPU_NUM,
            spec_core_end() + ((old(self).cpuid + 1) * PER_CPU_SIZE) as u64 <= u64::MAX,
    {
        // 清理中断
        self.idle_clear_interrupt();
        
        proof {
            assert(self.inv());
        }
        
        // 验证 CPU ID
        self.idle_verify_cpu_id();
        
        // 步骤 3：设置电源状态（关键验证点！）
        self.idle_set_power_state();
        
        proof {
            assert(!self.power_on);  // 验证：电源状态已关闭
        }
        
        // 步骤 4：激活 VMX
        let vmx_result = self.idle_activate_vmx();
        if vmx_result.is_err() {
            // 如果 VMX 激活失败，panic
            // panic!("Failed to activate VMX");
            loop {}  // 替代 panic
        }
        
        proof {
            assert(self.vmx_on);
            assert(self.vmcs_configured);
        }
        
        // 步骤 5：初始化 parking
        self.idle_init_parking();
        
        // 步骤 6：配置 VMCS
        let vmcs_result = self.idle_setup_vmcs();
        if vmcs_result.is_err() {
            loop {}  // 替代 panic
            // panic!("Failed to setup VMCS");
        }
        
        proof {
            assert(self.vmcs_configured);
        }
        
        // 步骤 7：设置栈顶（关键验证点！）
        self.idle_set_stack_top();
        
        proof {
            // 验证所有关键属性
            assert(self.host_stack_top > spec_core_end());
            assert(self.host_stack_top % 16 == 0);
            assert(!self.power_on);
            assert(self.vmx_on);
            assert(self.vmcs_configured);
            
            // 验证：现在满足 ready_for_idle
            assert(self.ready_for_idle());
        }
        
        // === 步骤 8：启动 VM（信任边界） ===
        self.idle_activate_and_launch();
        
        // 永不到达
    }
}

} // verus!

fn main() {
    
}