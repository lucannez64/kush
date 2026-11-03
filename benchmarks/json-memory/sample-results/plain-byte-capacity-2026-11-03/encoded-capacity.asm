
/tmp/kush-headerless-confirm-binaries/kush-plain:     file format elf64-x86-64


Disassembly of section .init:

Disassembly of section .plt:

Disassembly of section .text:

0000000000004fd0 <kush_fn_7>:
    4fd0:	push   %rbp
    4fd1:	mov    %rsp,%rbp
    4fd4:	sub    $0x50,%rsp
    4fd8:	mov    %rbx,0x20(%rsp)
    4fdd:	mov    %r12,0x28(%rsp)
    4fe2:	mov    %r13,0x30(%rsp)
    4fe7:	mov    %r14,0x38(%rsp)
    4fec:	mov    %r15,0x40(%rsp)
    4ff1:	mov    %rdx,%rbx
    4ff4:	mov    %rdi,%r12
    4ff7:	mov    %rsi,%r15
    4ffa:	lea    0x1b7bf(%rip),%rax        # 207c0 <kush_handler_depth>
    5001:	call   *%rax
    5003:	mov    %rax,0x18(%rsp)
    5008:	movq   $0x0,(%rsp)
    5010:	movq   $0x0,0x8(%rsp)
    5019:	mov    %r12,%rdi
    501c:	mov    %rdi,(%rsp)
    5020:	mov    %rdi,0x8(%rsp)
    5025:	mov    %rbx,%r12
    5028:	mov    %r12,%rsi
    502b:	shr    $0x3f,%rsi
    502f:	add    %r12,%rsi
    5032:	and    $0xfffffffffffffffe,%rsi
    5036:	mov    %r12,%rdi
    5039:	sub    %rsi,%rdi
    503c:	cmp    $0x1,%rdi
    5040:	je     5050 <kush_fn_7+0x80>
    5046:	mov    $0x10,%ebx
    504b:	jmp    5055 <kush_fn_7+0x85>
    5050:	mov    $0x200,%ebx
    5055:	lea    0x1b764(%rip),%r9        # 207c0 <kush_handler_depth>
    505c:	call   *%r9
    505f:	xor    %r13,%r13
    5062:	xor    %ecx,%ecx
    5064:	mov    %r13,%rdi
    5067:	mov    %rcx,%r14
    506a:	mov    %r13,0x10(%rsp)
    506f:	cmp    %rbx,%r13
    5072:	jl     50e4 <kush_fn_7+0x114>
    5078:	mov    0x8(%rsp),%r12
    507d:	xor    %ebx,%ebx
    507f:	test   %cl,%cl
    5081:	je     508c <kush_fn_7+0xbc>
    5087:	call   2a2f <kush_drop_12>
    508c:	test   %r14b,%r14b
    508f:	je     509f <kush_fn_7+0xcf>
    5095:	mov    0x10(%rsp),%rdi
    509a:	call   2a2f <kush_drop_12>
    509f:	test   %bl,%bl
    50a1:	je     50b1 <kush_fn_7+0xe1>
    50a7:	mov    0x8(%rsp),%rdi
    50ac:	call   2a2f <kush_drop_12>
    50b1:	lea    0x1b748(%rip),%rax        # 20800 <kush_handler_restore>
    50b8:	mov    0x18(%rsp),%rdi
    50bd:	call   *%rax
    50bf:	mov    %r12,%rax
    50c2:	mov    0x20(%rsp),%rbx
    50c7:	mov    0x28(%rsp),%r12
    50cc:	mov    0x30(%rsp),%r13
    50d1:	mov    0x38(%rsp),%r14
    50d6:	mov    0x40(%rsp),%r15
    50db:	add    $0x50,%rsp
    50df:	mov    %rbp,%rsp
    50e2:	pop    %rbp
    50e3:	ret
    50e4:	mov    0x8(%rsp),%rdi
    50e9:	mov    %r15,%r14
    50ec:	mov    %r14,%rcx
    50ef:	add    %r12,%rcx
    50f2:	seto   %al
    50f5:	test   %al,%al
    50f7:	jne    51ef <kush_fn_7+0x21f>
    50fd:	add    %r13,%rcx
    5100:	seto   %al
    5103:	test   %al,%al
    5105:	jne    51e4 <kush_fn_7+0x214>
    510b:	mov    $0x41,%esi
    5110:	mov    %rcx,%rax
    5113:	imulq  0xe6(%rip)        # 5200 <kush_fn_7+0x230>
    511a:	sar    $0x3,%rdx
    511e:	mov    %rdx,%rax
    5121:	shr    $0x3f,%rax
    5125:	add    %rdx,%rax
    5128:	imul   $0x1a,%rax,%rax
    512c:	sub    %rax,%rcx
    512f:	add    %rcx,%rsi
    5132:	seto   %al
    5135:	test   %al,%al
    5137:	jne    51d9 <kush_fn_7+0x209>
    513d:	cmp    $0xff,%rsi
    5144:	ja     51ce <kush_fn_7+0x1fe>
    514a:	mov    (%rdi),%rcx
    514d:	mov    0x8(%rdi),%rax
    5151:	mov    %rdi,0x10(%rsp)
    5156:	mov    %rax,%rdx
    5159:	and    $0xffff,%rdx
    5160:	test   %rax,%rax
    5163:	cmovl  %rdx,%rax
    5167:	cmp    %rax,%rcx
    516a:	jb     5189 <kush_fn_7+0x1b9>
    5170:	lea    0x18a19(%rip),%rax        # 1db90 <kush_bytes_push>
    5177:	mov    0x10(%rsp),%r15
    517c:	mov    %r15,%rdi
    517f:	call   *%rax
    5181:	mov    %rax,%rdi
    5184:	jmp    519d <kush_fn_7+0x1cd>
    5189:	mov    0x10(%rsp),%r15
    518e:	mov    %sil,0x10(%r15,%rcx,1)
    5193:	lea    0x1(%rcx),%rax
    5197:	mov    %rax,(%r15)
    519a:	mov    %r15,%rdi
    519d:	mov    %rdi,0x8(%rsp)
    51a2:	add    $0x1,%r13
    51a6:	seto   %al
    51a9:	test   %al,%al
    51ab:	jne    51c3 <kush_fn_7+0x1f3>
    51b1:	xor    %ecx,%ecx
    51b3:	mov    %r15,0x10(%rsp)
    51b8:	mov    %r14,%r15
    51bb:	mov    %rcx,%r14
    51be:	jmp    506f <kush_fn_7+0x9f>
    51c3:	lea    0x162b6(%rip),%rax        # 1b480 <kush_panic>
    51ca:	call   *%rax
    51cc:	ud2
    51ce:	lea    0x162ab(%rip),%rax        # 1b480 <kush_panic>
    51d5:	call   *%rax
    51d7:	ud2
    51d9:	lea    0x162a0(%rip),%rax        # 1b480 <kush_panic>
    51e0:	call   *%rax
    51e2:	ud2
    51e4:	lea    0x16295(%rip),%rax        # 1b480 <kush_panic>
    51eb:	call   *%rax
    51ed:	ud2
    51ef:	lea    0x1628a(%rip),%rax        # 1b480 <kush_panic>
    51f6:	call   *%rax
    51f8:	ud2
    51fa:	add    %al,(%rax)
    51fc:	add    %al,(%rax)
    51fe:	add    %al,(%rax)
    5200:	(bad)
    5203:	(bad)
    5204:	rex.WRX in (%dx),%al
    5206:	.byte 0xc4
    5207:	rex.WRX

Disassembly of section .fini:
