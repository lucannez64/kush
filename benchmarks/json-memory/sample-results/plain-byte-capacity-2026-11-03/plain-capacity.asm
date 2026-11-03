
/tmp/kush-byte-access-confirm/kush-plain-capacity:     file format elf64-x86-64


Disassembly of section .init:

Disassembly of section .plt:

Disassembly of section .text:

0000000000004fa8 <kush_fn_7>:
    4fa8:	push   %rbp
    4fa9:	mov    %rsp,%rbp
    4fac:	sub    $0x50,%rsp
    4fb0:	mov    %rbx,0x20(%rsp)
    4fb5:	mov    %r12,0x28(%rsp)
    4fba:	mov    %r13,0x30(%rsp)
    4fbf:	mov    %r14,0x38(%rsp)
    4fc4:	mov    %r15,0x40(%rsp)
    4fc9:	mov    %rdx,%rbx
    4fcc:	mov    %rdi,%r12
    4fcf:	mov    %rsi,%r15
    4fd2:	lea    0x1b5d7(%rip),%rax        # 205b0 <kush_handler_depth>
    4fd9:	call   *%rax
    4fdb:	mov    %rax,0x18(%rsp)
    4fe0:	movq   $0x0,(%rsp)
    4fe8:	movq   $0x0,0x8(%rsp)
    4ff1:	mov    %r12,%rdi
    4ff4:	mov    %rdi,(%rsp)
    4ff8:	mov    %rdi,0x8(%rsp)
    4ffd:	mov    %rbx,%r12
    5000:	mov    %r12,%rsi
    5003:	shr    $0x3f,%rsi
    5007:	lea    (%r12,%rsi,1),%rdx
    500b:	and    $0xfffffffffffffffe,%rdx
    500f:	mov    %r12,%rsi
    5012:	sub    %rdx,%rsi
    5015:	cmp    $0x1,%rsi
    5019:	je     5029 <kush_fn_7+0x81>
    501f:	mov    $0x10,%ebx
    5024:	jmp    502e <kush_fn_7+0x86>
    5029:	mov    $0x200,%ebx
    502e:	lea    0x1b57b(%rip),%rdi        # 205b0 <kush_handler_depth>
    5035:	call   *%rdi
    5037:	xor    %r13,%r13
    503a:	xor    %ecx,%ecx
    503c:	mov    %r13,%rdi
    503f:	mov    %rcx,%r14
    5042:	mov    %r13,0x10(%rsp)
    5047:	cmp    %rbx,%r13
    504a:	jl     50bc <kush_fn_7+0x114>
    5050:	mov    0x8(%rsp),%r12
    5055:	xor    %ebx,%ebx
    5057:	test   %cl,%cl
    5059:	je     5064 <kush_fn_7+0xbc>
    505f:	call   2a2f <kush_drop_12>
    5064:	test   %r14b,%r14b
    5067:	je     5077 <kush_fn_7+0xcf>
    506d:	mov    0x10(%rsp),%rdi
    5072:	call   2a2f <kush_drop_12>
    5077:	test   %bl,%bl
    5079:	je     5089 <kush_fn_7+0xe1>
    507f:	mov    0x8(%rsp),%rdi
    5084:	call   2a2f <kush_drop_12>
    5089:	lea    0x1b560(%rip),%rax        # 205f0 <kush_handler_restore>
    5090:	mov    0x18(%rsp),%rdi
    5095:	call   *%rax
    5097:	mov    %r12,%rax
    509a:	mov    0x20(%rsp),%rbx
    509f:	mov    0x28(%rsp),%r12
    50a4:	mov    0x30(%rsp),%r13
    50a9:	mov    0x38(%rsp),%r14
    50ae:	mov    0x40(%rsp),%r15
    50b3:	add    $0x50,%rsp
    50b7:	mov    %rbp,%rsp
    50ba:	pop    %rbp
    50bb:	ret
    50bc:	mov    0x8(%rsp),%rdi
    50c1:	mov    %r15,%r14
    50c4:	mov    %r14,%rcx
    50c7:	add    %r12,%rcx
    50ca:	seto   %al
    50cd:	test   %al,%al
    50cf:	jne    51b6 <kush_fn_7+0x20e>
    50d5:	add    %r13,%rcx
    50d8:	seto   %al
    50db:	test   %al,%al
    50dd:	jne    51ab <kush_fn_7+0x203>
    50e3:	mov    $0x41,%esi
    50e8:	mov    %rcx,%rax
    50eb:	imulq  0xd6(%rip)        # 51c8 <kush_fn_7+0x220>
    50f2:	sar    $0x3,%rdx
    50f6:	mov    %rdx,%rax
    50f9:	shr    $0x3f,%rax
    50fd:	add    %rdx,%rax
    5100:	imul   $0x1a,%rax,%rax
    5104:	sub    %rax,%rcx
    5107:	add    %rcx,%rsi
    510a:	seto   %al
    510d:	test   %al,%al
    510f:	jne    51a0 <kush_fn_7+0x1f8>
    5115:	cmp    $0xff,%rsi
    511c:	ja     5195 <kush_fn_7+0x1ed>
    5122:	mov    (%rdi),%rcx
    5125:	mov    0x8(%rdi),%rax
    5129:	mov    %rdi,0x10(%rsp)
    512e:	cmp    %rax,%rcx
    5131:	jb     5150 <kush_fn_7+0x1a8>
    5137:	lea    0x188f2(%rip),%rax        # 1da30 <kush_bytes_push>
    513e:	mov    0x10(%rsp),%r15
    5143:	mov    %r15,%rdi
    5146:	call   *%rax
    5148:	mov    %rax,%rdi
    514b:	jmp    5164 <kush_fn_7+0x1bc>
    5150:	mov    0x10(%rsp),%r15
    5155:	mov    %sil,0x10(%r15,%rcx,1)
    515a:	lea    0x1(%rcx),%rax
    515e:	mov    %rax,(%r15)
    5161:	mov    %r15,%rdi
    5164:	mov    %rdi,0x8(%rsp)
    5169:	add    $0x1,%r13
    516d:	seto   %al
    5170:	test   %al,%al
    5172:	jne    518a <kush_fn_7+0x1e2>
    5178:	xor    %ecx,%ecx
    517a:	mov    %r15,0x10(%rsp)
    517f:	mov    %r14,%r15
    5182:	mov    %rcx,%r14
    5185:	jmp    5047 <kush_fn_7+0x9f>
    518a:	lea    0x161af(%rip),%rax        # 1b340 <kush_panic>
    5191:	call   *%rax
    5193:	ud2
    5195:	lea    0x161a4(%rip),%rax        # 1b340 <kush_panic>
    519c:	call   *%rax
    519e:	ud2
    51a0:	lea    0x16199(%rip),%rax        # 1b340 <kush_panic>
    51a7:	call   *%rax
    51a9:	ud2
    51ab:	lea    0x1618e(%rip),%rax        # 1b340 <kush_panic>
    51b2:	call   *%rax
    51b4:	ud2
    51b6:	lea    0x16183(%rip),%rax        # 1b340 <kush_panic>
    51bd:	call   *%rax
    51bf:	ud2
    51c1:	add    %al,(%rax)
    51c3:	add    %al,(%rax)
    51c5:	add    %al,(%rax)
    51c7:	add    %al,%ch
    51c9:	rex.WRX in (%dx),%al
    51cb:	(bad)
    51cc:	rex.WRX in (%dx),%al
    51ce:	.byte 0xc4
    51cf:	rex.WRX

Disassembly of section .fini:
