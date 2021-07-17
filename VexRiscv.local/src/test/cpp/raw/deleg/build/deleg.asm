
build/deleg.elf:     file format elf32-littleriscv


Disassembly of section .crt_section:

80000000 <_start>:
80000000:	00100e93          	li	t4,1
80000004:	00001097          	auipc	ra,0x1
80000008:	a3c08093          	addi	ra,ra,-1476 # 80000a40 <mtrap>
8000000c:	30509073          	csrw	mtvec,ra
80000010:	00001097          	auipc	ra,0x1
80000014:	a6808093          	addi	ra,ra,-1432 # 80000a78 <strap>
80000018:	10509073          	csrw	stvec,ra
8000001c:	f00110b7          	lui	ra,0xf0011
80000020:	00000113          	li	sp,0
80000024:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
80000028:	00000013          	nop
8000002c:	00000013          	nop
80000030:	00000013          	nop
80000034:	00000013          	nop
80000038:	00000013          	nop
8000003c:	00000013          	nop
80000040:	00000013          	nop
80000044:	00000013          	nop

80000048 <test1>:
80000048:	00100e13          	li	t3,1
8000004c:	00000f17          	auipc	t5,0x0
80000050:	00cf0f13          	addi	t5,t5,12 # 80000058 <test2>
80000054:	00000073          	ecall

80000058 <test2>:
80000058:	00200e13          	li	t3,2
8000005c:	000020b7          	lui	ra,0x2
80000060:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000064:	00000113          	li	sp,0
80000068:	3000b073          	csrc	mstatus,ra
8000006c:	30012073          	csrs	mstatus,sp
80000070:	00000097          	auipc	ra,0x0
80000074:	01408093          	addi	ra,ra,20 # 80000084 <test2+0x2c>
80000078:	34109073          	csrw	mepc,ra
8000007c:	30200073          	mret
80000080:	1a90006f          	j	80000a28 <fail>
80000084:	00000f17          	auipc	t5,0x0
80000088:	024f0f13          	addi	t5,t5,36 # 800000a8 <test4>
8000008c:	00000073          	ecall
80000090:	1990006f          	j	80000a28 <fail>

80000094 <test3>:
80000094:	00300e13          	li	t3,3
80000098:	00000f17          	auipc	t5,0x0
8000009c:	010f0f13          	addi	t5,t5,16 # 800000a8 <test4>
800000a0:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
800000a4:	1850006f          	j	80000a28 <fail>

800000a8 <test4>:
800000a8:	00400e13          	li	t3,4
800000ac:	000020b7          	lui	ra,0x2
800000b0:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
800000b4:	00001137          	lui	sp,0x1
800000b8:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
800000bc:	3000b073          	csrc	mstatus,ra
800000c0:	30012073          	csrs	mstatus,sp
800000c4:	00000097          	auipc	ra,0x0
800000c8:	01408093          	addi	ra,ra,20 # 800000d8 <test4+0x30>
800000cc:	34109073          	csrw	mepc,ra
800000d0:	30200073          	mret
800000d4:	1550006f          	j	80000a28 <fail>
800000d8:	00000f17          	auipc	t5,0x0
800000dc:	010f0f13          	addi	t5,t5,16 # 800000e8 <test5>
800000e0:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
800000e4:	1450006f          	j	80000a28 <fail>

800000e8 <test5>:
800000e8:	00500e13          	li	t3,5
800000ec:	000020b7          	lui	ra,0x2
800000f0:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
800000f4:	00000113          	li	sp,0
800000f8:	3000b073          	csrc	mstatus,ra
800000fc:	30012073          	csrs	mstatus,sp
80000100:	00000097          	auipc	ra,0x0
80000104:	01408093          	addi	ra,ra,20 # 80000114 <test5+0x2c>
80000108:	34109073          	csrw	mepc,ra
8000010c:	30200073          	mret
80000110:	1190006f          	j	80000a28 <fail>
80000114:	00000f17          	auipc	t5,0x0
80000118:	010f0f13          	addi	t5,t5,16 # 80000124 <test6>
8000011c:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
80000120:	1090006f          	j	80000a28 <fail>

80000124 <test6>:
80000124:	00600e13          	li	t3,6
80000128:	01000093          	li	ra,16
8000012c:	30209073          	csrw	medeleg,ra

80000130 <test7>:
80000130:	00700e13          	li	t3,7
80000134:	00000f17          	auipc	t5,0x0
80000138:	010f0f13          	addi	t5,t5,16 # 80000144 <test8>
8000013c:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
80000140:	0e90006f          	j	80000a28 <fail>

80000144 <test8>:
80000144:	00800e13          	li	t3,8
80000148:	00000f17          	auipc	t5,0x0
8000014c:	03cf0f13          	addi	t5,t5,60 # 80000184 <test9>
80000150:	000020b7          	lui	ra,0x2
80000154:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000158:	00001137          	lui	sp,0x1
8000015c:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
80000160:	3000b073          	csrc	mstatus,ra
80000164:	30012073          	csrs	mstatus,sp
80000168:	00000097          	auipc	ra,0x0
8000016c:	01408093          	addi	ra,ra,20 # 8000017c <test8+0x38>
80000170:	34109073          	csrw	mepc,ra
80000174:	30200073          	mret
80000178:	0b10006f          	j	80000a28 <fail>
8000017c:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
80000180:	0a90006f          	j	80000a28 <fail>

80000184 <test9>:
80000184:	00900e13          	li	t3,9
80000188:	00000f17          	auipc	t5,0x0
8000018c:	038f0f13          	addi	t5,t5,56 # 800001c0 <test10>
80000190:	000020b7          	lui	ra,0x2
80000194:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000198:	00000113          	li	sp,0
8000019c:	3000b073          	csrc	mstatus,ra
800001a0:	30012073          	csrs	mstatus,sp
800001a4:	00000097          	auipc	ra,0x0
800001a8:	01408093          	addi	ra,ra,20 # 800001b8 <test9+0x34>
800001ac:	34109073          	csrw	mepc,ra
800001b0:	30200073          	mret
800001b4:	0750006f          	j	80000a28 <fail>
800001b8:	00102083          	lw	ra,1(zero) # 1 <_start-0x7fffffff>
800001bc:	06d0006f          	j	80000a28 <fail>

800001c0 <test10>:
800001c0:	00a00e13          	li	t3,10
800001c4:	00000f17          	auipc	t5,0x0
800001c8:	07cf0f13          	addi	t5,t5,124 # 80000240 <test11>
800001cc:	f00110b7          	lui	ra,0xf0011
800001d0:	00000113          	li	sp,0
800001d4:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
800001d8:	00000013          	nop
800001dc:	00000013          	nop
800001e0:	00000013          	nop
800001e4:	00000013          	nop
800001e8:	00000013          	nop
800001ec:	00000013          	nop
800001f0:	00000013          	nop
800001f4:	00000013          	nop
800001f8:	00800093          	li	ra,8
800001fc:	30009073          	csrw	mstatus,ra
80000200:	000010b7          	lui	ra,0x1
80000204:	80008093          	addi	ra,ra,-2048 # 800 <_start-0x7ffff800>
80000208:	30409073          	csrw	mie,ra
8000020c:	f00110b7          	lui	ra,0xf0011
80000210:	00100113          	li	sp,1
80000214:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
80000218:	00000013          	nop
8000021c:	00000013          	nop
80000220:	00000013          	nop
80000224:	00000013          	nop
80000228:	00000013          	nop
8000022c:	00000013          	nop
80000230:	00000013          	nop
80000234:	00000013          	nop
80000238:	10500073          	wfi
8000023c:	7ec0006f          	j	80000a28 <fail>

80000240 <test11>:
80000240:	00b00e13          	li	t3,11
80000244:	00000f17          	auipc	t5,0x0
80000248:	0a8f0f13          	addi	t5,t5,168 # 800002ec <test12>
8000024c:	f00110b7          	lui	ra,0xf0011
80000250:	00000113          	li	sp,0
80000254:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
80000258:	00000013          	nop
8000025c:	00000013          	nop
80000260:	00000013          	nop
80000264:	00000013          	nop
80000268:	00000013          	nop
8000026c:	00000013          	nop
80000270:	00000013          	nop
80000274:	00000013          	nop
80000278:	00800093          	li	ra,8
8000027c:	30009073          	csrw	mstatus,ra
80000280:	000010b7          	lui	ra,0x1
80000284:	80008093          	addi	ra,ra,-2048 # 800 <_start-0x7ffff800>
80000288:	30409073          	csrw	mie,ra
8000028c:	000020b7          	lui	ra,0x2
80000290:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000294:	00001137          	lui	sp,0x1
80000298:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
8000029c:	3000b073          	csrc	mstatus,ra
800002a0:	30012073          	csrs	mstatus,sp
800002a4:	00000097          	auipc	ra,0x0
800002a8:	01408093          	addi	ra,ra,20 # 800002b8 <test11+0x78>
800002ac:	34109073          	csrw	mepc,ra
800002b0:	30200073          	mret
800002b4:	7740006f          	j	80000a28 <fail>
800002b8:	f00110b7          	lui	ra,0xf0011
800002bc:	00100113          	li	sp,1
800002c0:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
800002c4:	00000013          	nop
800002c8:	00000013          	nop
800002cc:	00000013          	nop
800002d0:	00000013          	nop
800002d4:	00000013          	nop
800002d8:	00000013          	nop
800002dc:	00000013          	nop
800002e0:	00000013          	nop
800002e4:	10500073          	wfi
800002e8:	7400006f          	j	80000a28 <fail>

800002ec <test12>:
800002ec:	00c00e13          	li	t3,12
800002f0:	00000f17          	auipc	t5,0x0
800002f4:	0a4f0f13          	addi	t5,t5,164 # 80000394 <test14>
800002f8:	f00110b7          	lui	ra,0xf0011
800002fc:	00000113          	li	sp,0
80000300:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
80000304:	00000013          	nop
80000308:	00000013          	nop
8000030c:	00000013          	nop
80000310:	00000013          	nop
80000314:	00000013          	nop
80000318:	00000013          	nop
8000031c:	00000013          	nop
80000320:	00000013          	nop
80000324:	00800093          	li	ra,8
80000328:	30009073          	csrw	mstatus,ra
8000032c:	000010b7          	lui	ra,0x1
80000330:	80008093          	addi	ra,ra,-2048 # 800 <_start-0x7ffff800>
80000334:	30409073          	csrw	mie,ra
80000338:	000020b7          	lui	ra,0x2
8000033c:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000340:	00000113          	li	sp,0
80000344:	3000b073          	csrc	mstatus,ra
80000348:	30012073          	csrs	mstatus,sp
8000034c:	00000097          	auipc	ra,0x0
80000350:	01408093          	addi	ra,ra,20 # 80000360 <test12+0x74>
80000354:	34109073          	csrw	mepc,ra
80000358:	30200073          	mret
8000035c:	6cc0006f          	j	80000a28 <fail>
80000360:	f00110b7          	lui	ra,0xf0011
80000364:	00100113          	li	sp,1
80000368:	0020a023          	sw	sp,0(ra) # f0011000 <strap+0x70010588>
8000036c:	00000013          	nop
80000370:	00000013          	nop
80000374:	00000013          	nop
80000378:	00000013          	nop
8000037c:	00000013          	nop
80000380:	00000013          	nop
80000384:	00000013          	nop
80000388:	00000013          	nop
8000038c:	10500073          	wfi
80000390:	6980006f          	j	80000a28 <fail>

80000394 <test14>:
80000394:	00200093          	li	ra,2
80000398:	10009073          	csrw	sstatus,ra
8000039c:	00e00e13          	li	t3,14
800003a0:	00000f17          	auipc	t5,0x0
800003a4:	080f0f13          	addi	t5,t5,128 # 80000420 <test15>
800003a8:	f00120b7          	lui	ra,0xf0012
800003ac:	00000113          	li	sp,0
800003b0:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800003b4:	00000013          	nop
800003b8:	00000013          	nop
800003bc:	00000013          	nop
800003c0:	00000013          	nop
800003c4:	00000013          	nop
800003c8:	00000013          	nop
800003cc:	00000013          	nop
800003d0:	00000013          	nop
800003d4:	00200093          	li	ra,2
800003d8:	30009073          	csrw	mstatus,ra
800003dc:	20000093          	li	ra,512
800003e0:	30409073          	csrw	mie,ra
800003e4:	00000e93          	li	t4,0
800003e8:	f00120b7          	lui	ra,0xf0012
800003ec:	00100113          	li	sp,1
800003f0:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800003f4:	00000013          	nop
800003f8:	00000013          	nop
800003fc:	00000013          	nop
80000400:	00000013          	nop
80000404:	00000013          	nop
80000408:	00000013          	nop
8000040c:	00000013          	nop
80000410:	00000013          	nop
80000414:	06400093          	li	ra,100
80000418:	fff08093          	addi	ra,ra,-1
8000041c:	fe104ee3          	bgtz	ra,80000418 <test14+0x84>

80000420 <test15>:
80000420:	00f00e13          	li	t3,15
80000424:	00000f17          	auipc	t5,0x0
80000428:	0a8f0f13          	addi	t5,t5,168 # 800004cc <test16>
8000042c:	f00120b7          	lui	ra,0xf0012
80000430:	00000113          	li	sp,0
80000434:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000438:	00000013          	nop
8000043c:	00000013          	nop
80000440:	00000013          	nop
80000444:	00000013          	nop
80000448:	00000013          	nop
8000044c:	00000013          	nop
80000450:	00000013          	nop
80000454:	00000013          	nop
80000458:	00200093          	li	ra,2
8000045c:	30009073          	csrw	mstatus,ra
80000460:	20000093          	li	ra,512
80000464:	30409073          	csrw	mie,ra
80000468:	000020b7          	lui	ra,0x2
8000046c:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000470:	00001137          	lui	sp,0x1
80000474:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
80000478:	3000b073          	csrc	mstatus,ra
8000047c:	30012073          	csrs	mstatus,sp
80000480:	00000097          	auipc	ra,0x0
80000484:	01408093          	addi	ra,ra,20 # 80000494 <test15+0x74>
80000488:	34109073          	csrw	mepc,ra
8000048c:	30200073          	mret
80000490:	5980006f          	j	80000a28 <fail>
80000494:	00100e93          	li	t4,1
80000498:	f00120b7          	lui	ra,0xf0012
8000049c:	00100113          	li	sp,1
800004a0:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800004a4:	00000013          	nop
800004a8:	00000013          	nop
800004ac:	00000013          	nop
800004b0:	00000013          	nop
800004b4:	00000013          	nop
800004b8:	00000013          	nop
800004bc:	00000013          	nop
800004c0:	00000013          	nop
800004c4:	10500073          	wfi
800004c8:	5600006f          	j	80000a28 <fail>

800004cc <test16>:
800004cc:	01000e13          	li	t3,16
800004d0:	00000f17          	auipc	t5,0x0
800004d4:	0a0f0f13          	addi	t5,t5,160 # 80000570 <test17>
800004d8:	f00120b7          	lui	ra,0xf0012
800004dc:	00000113          	li	sp,0
800004e0:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800004e4:	00000013          	nop
800004e8:	00000013          	nop
800004ec:	00000013          	nop
800004f0:	00000013          	nop
800004f4:	00000013          	nop
800004f8:	00000013          	nop
800004fc:	00000013          	nop
80000500:	00000013          	nop
80000504:	00200093          	li	ra,2
80000508:	30009073          	csrw	mstatus,ra
8000050c:	20000093          	li	ra,512
80000510:	30409073          	csrw	mie,ra
80000514:	000020b7          	lui	ra,0x2
80000518:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
8000051c:	00000113          	li	sp,0
80000520:	3000b073          	csrc	mstatus,ra
80000524:	30012073          	csrs	mstatus,sp
80000528:	00000097          	auipc	ra,0x0
8000052c:	01408093          	addi	ra,ra,20 # 8000053c <test16+0x70>
80000530:	34109073          	csrw	mepc,ra
80000534:	30200073          	mret
80000538:	4f00006f          	j	80000a28 <fail>
8000053c:	f00120b7          	lui	ra,0xf0012
80000540:	00100113          	li	sp,1
80000544:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000548:	00000013          	nop
8000054c:	00000013          	nop
80000550:	00000013          	nop
80000554:	00000013          	nop
80000558:	00000013          	nop
8000055c:	00000013          	nop
80000560:	00000013          	nop
80000564:	00000013          	nop
80000568:	10500073          	wfi
8000056c:	4bc0006f          	j	80000a28 <fail>

80000570 <test17>:
80000570:	01100e13          	li	t3,17
80000574:	20000093          	li	ra,512
80000578:	30309073          	csrw	mideleg,ra
8000057c:	00000f17          	auipc	t5,0x0
80000580:	080f0f13          	addi	t5,t5,128 # 800005fc <test18>
80000584:	f00120b7          	lui	ra,0xf0012
80000588:	00000113          	li	sp,0
8000058c:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000590:	00000013          	nop
80000594:	00000013          	nop
80000598:	00000013          	nop
8000059c:	00000013          	nop
800005a0:	00000013          	nop
800005a4:	00000013          	nop
800005a8:	00000013          	nop
800005ac:	00000013          	nop
800005b0:	00200093          	li	ra,2
800005b4:	30009073          	csrw	mstatus,ra
800005b8:	20000093          	li	ra,512
800005bc:	30409073          	csrw	mie,ra
800005c0:	00000e93          	li	t4,0
800005c4:	f00120b7          	lui	ra,0xf0012
800005c8:	00100113          	li	sp,1
800005cc:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800005d0:	00000013          	nop
800005d4:	00000013          	nop
800005d8:	00000013          	nop
800005dc:	00000013          	nop
800005e0:	00000013          	nop
800005e4:	00000013          	nop
800005e8:	00000013          	nop
800005ec:	00000013          	nop
800005f0:	06400093          	li	ra,100
800005f4:	fff08093          	addi	ra,ra,-1
800005f8:	fe104ee3          	bgtz	ra,800005f4 <test17+0x84>

800005fc <test18>:
800005fc:	01200e13          	li	t3,18
80000600:	00000f17          	auipc	t5,0x0
80000604:	0a8f0f13          	addi	t5,t5,168 # 800006a8 <test19>
80000608:	f00120b7          	lui	ra,0xf0012
8000060c:	00000113          	li	sp,0
80000610:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000614:	00000013          	nop
80000618:	00000013          	nop
8000061c:	00000013          	nop
80000620:	00000013          	nop
80000624:	00000013          	nop
80000628:	00000013          	nop
8000062c:	00000013          	nop
80000630:	00000013          	nop
80000634:	00200093          	li	ra,2
80000638:	30009073          	csrw	mstatus,ra
8000063c:	20000093          	li	ra,512
80000640:	30409073          	csrw	mie,ra
80000644:	000020b7          	lui	ra,0x2
80000648:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
8000064c:	00001137          	lui	sp,0x1
80000650:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
80000654:	3000b073          	csrc	mstatus,ra
80000658:	30012073          	csrs	mstatus,sp
8000065c:	00000097          	auipc	ra,0x0
80000660:	01408093          	addi	ra,ra,20 # 80000670 <test18+0x74>
80000664:	34109073          	csrw	mepc,ra
80000668:	30200073          	mret
8000066c:	3bc0006f          	j	80000a28 <fail>
80000670:	00100e93          	li	t4,1
80000674:	f00120b7          	lui	ra,0xf0012
80000678:	00100113          	li	sp,1
8000067c:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000680:	00000013          	nop
80000684:	00000013          	nop
80000688:	00000013          	nop
8000068c:	00000013          	nop
80000690:	00000013          	nop
80000694:	00000013          	nop
80000698:	00000013          	nop
8000069c:	00000013          	nop
800006a0:	10500073          	wfi
800006a4:	3840006f          	j	80000a28 <fail>

800006a8 <test19>:
800006a8:	01300e13          	li	t3,19
800006ac:	00000f17          	auipc	t5,0x0
800006b0:	0a0f0f13          	addi	t5,t5,160 # 8000074c <test20>
800006b4:	f00120b7          	lui	ra,0xf0012
800006b8:	00000113          	li	sp,0
800006bc:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800006c0:	00000013          	nop
800006c4:	00000013          	nop
800006c8:	00000013          	nop
800006cc:	00000013          	nop
800006d0:	00000013          	nop
800006d4:	00000013          	nop
800006d8:	00000013          	nop
800006dc:	00000013          	nop
800006e0:	00200093          	li	ra,2
800006e4:	30009073          	csrw	mstatus,ra
800006e8:	20000093          	li	ra,512
800006ec:	30409073          	csrw	mie,ra
800006f0:	000020b7          	lui	ra,0x2
800006f4:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
800006f8:	00000113          	li	sp,0
800006fc:	3000b073          	csrc	mstatus,ra
80000700:	30012073          	csrs	mstatus,sp
80000704:	00000097          	auipc	ra,0x0
80000708:	01408093          	addi	ra,ra,20 # 80000718 <test19+0x70>
8000070c:	34109073          	csrw	mepc,ra
80000710:	30200073          	mret
80000714:	3140006f          	j	80000a28 <fail>
80000718:	f00120b7          	lui	ra,0xf0012
8000071c:	00100113          	li	sp,1
80000720:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000724:	00000013          	nop
80000728:	00000013          	nop
8000072c:	00000013          	nop
80000730:	00000013          	nop
80000734:	00000013          	nop
80000738:	00000013          	nop
8000073c:	00000013          	nop
80000740:	00000013          	nop
80000744:	10500073          	wfi
80000748:	2e00006f          	j	80000a28 <fail>

8000074c <test20>:
8000074c:	f00120b7          	lui	ra,0xf0012
80000750:	00000113          	li	sp,0
80000754:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000758:	00000013          	nop
8000075c:	00000013          	nop
80000760:	00000013          	nop
80000764:	00000013          	nop
80000768:	00000013          	nop
8000076c:	00000013          	nop
80000770:	00000013          	nop
80000774:	00000013          	nop
80000778:	01400e13          	li	t3,20
8000077c:	00000f17          	auipc	t5,0x0
80000780:	030f0f13          	addi	t5,t5,48 # 800007ac <test21>
80000784:	00200093          	li	ra,2
80000788:	30009073          	csrw	mstatus,ra
8000078c:	20000093          	li	ra,512
80000790:	30409073          	csrw	mie,ra
80000794:	00000e93          	li	t4,0
80000798:	20000093          	li	ra,512
8000079c:	1440a073          	csrs	sip,ra
800007a0:	06400093          	li	ra,100
800007a4:	fff08093          	addi	ra,ra,-1
800007a8:	fe104ee3          	bgtz	ra,800007a4 <test20+0x58>

800007ac <test21>:
800007ac:	01500e13          	li	t3,21
800007b0:	00000f17          	auipc	t5,0x0
800007b4:	060f0f13          	addi	t5,t5,96 # 80000810 <test22>
800007b8:	20000093          	li	ra,512
800007bc:	1440b073          	csrc	sip,ra
800007c0:	00200093          	li	ra,2
800007c4:	30009073          	csrw	mstatus,ra
800007c8:	20000093          	li	ra,512
800007cc:	30409073          	csrw	mie,ra
800007d0:	000020b7          	lui	ra,0x2
800007d4:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
800007d8:	00001137          	lui	sp,0x1
800007dc:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
800007e0:	3000b073          	csrc	mstatus,ra
800007e4:	30012073          	csrs	mstatus,sp
800007e8:	00000097          	auipc	ra,0x0
800007ec:	01408093          	addi	ra,ra,20 # 800007fc <test21+0x50>
800007f0:	34109073          	csrw	mepc,ra
800007f4:	30200073          	mret
800007f8:	2300006f          	j	80000a28 <fail>
800007fc:	00100e93          	li	t4,1
80000800:	20000093          	li	ra,512
80000804:	1440a073          	csrs	sip,ra
80000808:	10500073          	wfi
8000080c:	21c0006f          	j	80000a28 <fail>

80000810 <test22>:
80000810:	01600e13          	li	t3,22
80000814:	00000f17          	auipc	t5,0x0
80000818:	058f0f13          	addi	t5,t5,88 # 8000086c <test23>
8000081c:	20000093          	li	ra,512
80000820:	1440b073          	csrc	sip,ra
80000824:	00200093          	li	ra,2
80000828:	30009073          	csrw	mstatus,ra
8000082c:	20000093          	li	ra,512
80000830:	30409073          	csrw	mie,ra
80000834:	20000093          	li	ra,512
80000838:	1440a073          	csrs	sip,ra
8000083c:	000020b7          	lui	ra,0x2
80000840:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000844:	00000113          	li	sp,0
80000848:	3000b073          	csrc	mstatus,ra
8000084c:	30012073          	csrs	mstatus,sp
80000850:	00000097          	auipc	ra,0x0
80000854:	01408093          	addi	ra,ra,20 # 80000864 <test22+0x54>
80000858:	34109073          	csrw	mepc,ra
8000085c:	30200073          	mret
80000860:	1c80006f          	j	80000a28 <fail>
80000864:	10500073          	wfi
80000868:	1c00006f          	j	80000a28 <fail>

8000086c <test23>:
8000086c:	01700e13          	li	t3,23
80000870:	00000e93          	li	t4,0
80000874:	f00120b7          	lui	ra,0xf0012
80000878:	00000113          	li	sp,0
8000087c:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000880:	00000013          	nop
80000884:	00000013          	nop
80000888:	00000013          	nop
8000088c:	00000013          	nop
80000890:	00000013          	nop
80000894:	00000013          	nop
80000898:	00000013          	nop
8000089c:	00000013          	nop
800008a0:	20000093          	li	ra,512
800008a4:	1440b073          	csrc	sip,ra
800008a8:	344021f3          	csrr	gp,mip
800008ac:	f00120b7          	lui	ra,0xf0012
800008b0:	00100113          	li	sp,1
800008b4:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800008b8:	00000013          	nop
800008bc:	00000013          	nop
800008c0:	00000013          	nop
800008c4:	00000013          	nop
800008c8:	00000013          	nop
800008cc:	00000013          	nop
800008d0:	00000013          	nop
800008d4:	00000013          	nop
800008d8:	20000093          	li	ra,512
800008dc:	1440b073          	csrc	sip,ra
800008e0:	344021f3          	csrr	gp,mip
800008e4:	f00120b7          	lui	ra,0xf0012
800008e8:	00000113          	li	sp,0
800008ec:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
800008f0:	00000013          	nop
800008f4:	00000013          	nop
800008f8:	00000013          	nop
800008fc:	00000013          	nop
80000900:	00000013          	nop
80000904:	00000013          	nop
80000908:	00000013          	nop
8000090c:	00000013          	nop
80000910:	20000093          	li	ra,512
80000914:	1440b073          	csrc	sip,ra
80000918:	344021f3          	csrr	gp,mip
8000091c:	f00120b7          	lui	ra,0xf0012
80000920:	00000113          	li	sp,0
80000924:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000928:	00000013          	nop
8000092c:	00000013          	nop
80000930:	00000013          	nop
80000934:	00000013          	nop
80000938:	00000013          	nop
8000093c:	00000013          	nop
80000940:	00000013          	nop
80000944:	00000013          	nop
80000948:	20000093          	li	ra,512
8000094c:	1440a073          	csrs	sip,ra
80000950:	344021f3          	csrr	gp,mip
80000954:	f00120b7          	lui	ra,0xf0012
80000958:	00100113          	li	sp,1
8000095c:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000960:	00000013          	nop
80000964:	00000013          	nop
80000968:	00000013          	nop
8000096c:	00000013          	nop
80000970:	00000013          	nop
80000974:	00000013          	nop
80000978:	00000013          	nop
8000097c:	00000013          	nop
80000980:	20000093          	li	ra,512
80000984:	1440a073          	csrs	sip,ra
80000988:	344021f3          	csrr	gp,mip
8000098c:	f00120b7          	lui	ra,0xf0012
80000990:	00000113          	li	sp,0
80000994:	0020a023          	sw	sp,0(ra) # f0012000 <strap+0x70011588>
80000998:	00000013          	nop
8000099c:	00000013          	nop
800009a0:	00000013          	nop
800009a4:	00000013          	nop
800009a8:	00000013          	nop
800009ac:	00000013          	nop
800009b0:	00000013          	nop
800009b4:	00000013          	nop

800009b8 <test24>:
800009b8:	01800e13          	li	t3,24
800009bc:	00200093          	li	ra,2
800009c0:	3040a073          	csrs	mie,ra
800009c4:	3440a073          	csrs	mip,ra
800009c8:	3000a073          	csrs	mstatus,ra
800009cc:	00100e93          	li	t4,1
800009d0:	00000f17          	auipc	t5,0x0
800009d4:	03cf0f13          	addi	t5,t5,60 # 80000a0c <test25>
800009d8:	000020b7          	lui	ra,0x2
800009dc:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
800009e0:	00001137          	lui	sp,0x1
800009e4:	80010113          	addi	sp,sp,-2048 # 800 <_start-0x7ffff800>
800009e8:	3000b073          	csrc	mstatus,ra
800009ec:	30012073          	csrs	mstatus,sp
800009f0:	00000097          	auipc	ra,0x0
800009f4:	01408093          	addi	ra,ra,20 # 80000a04 <test24_s>
800009f8:	34109073          	csrw	mepc,ra
800009fc:	30200073          	mret
80000a00:	0280006f          	j	80000a28 <fail>

80000a04 <test24_s>:
80000a04:	10500073          	wfi
80000a08:	0200006f          	j	80000a28 <fail>

80000a0c <test25>:
80000a0c:	01900e13          	li	t3,25
80000a10:	00000f17          	auipc	t5,0x0
80000a14:	014f0f13          	addi	t5,t5,20 # 80000a24 <test26>
80000a18:	30046073          	csrsi	mstatus,8
80000a1c:	10500073          	wfi
80000a20:	0080006f          	j	80000a28 <fail>

80000a24 <test26>:
80000a24:	0100006f          	j	80000a34 <pass>

80000a28 <fail>:
80000a28:	f0100137          	lui	sp,0xf0100
80000a2c:	f2410113          	addi	sp,sp,-220 # f00fff24 <strap+0x700ff4ac>
80000a30:	01c12023          	sw	t3,0(sp)

80000a34 <pass>:
80000a34:	f0100137          	lui	sp,0xf0100
80000a38:	f2010113          	addi	sp,sp,-224 # f00fff20 <strap+0x700ff4a8>
80000a3c:	00012023          	sw	zero,0(sp)

80000a40 <mtrap>:
80000a40:	fe0e84e3          	beqz	t4,80000a28 <fail>
80000a44:	342020f3          	csrr	ra,mcause
80000a48:	341020f3          	csrr	ra,mepc
80000a4c:	300020f3          	csrr	ra,mstatus
80000a50:	343020f3          	csrr	ra,mbadaddr
80000a54:	08000093          	li	ra,128
80000a58:	3000b073          	csrc	mstatus,ra
80000a5c:	00200093          	li	ra,2
80000a60:	fc1e8ae3          	beq	t4,ra,80000a34 <pass>
80000a64:	000020b7          	lui	ra,0x2
80000a68:	80008093          	addi	ra,ra,-2048 # 1800 <_start-0x7fffe800>
80000a6c:	3000a073          	csrs	mstatus,ra
80000a70:	341f1073          	csrw	mepc,t5
80000a74:	30200073          	mret

80000a78 <strap>:
80000a78:	fa0e88e3          	beqz	t4,80000a28 <fail>
80000a7c:	142020f3          	csrr	ra,scause
80000a80:	141020f3          	csrr	ra,sepc
80000a84:	100020f3          	csrr	ra,sstatus
80000a88:	143020f3          	csrr	ra,sbadaddr
80000a8c:	00000073          	ecall
80000a90:	00000013          	nop
80000a94:	00000013          	nop
80000a98:	00000013          	nop
80000a9c:	00000013          	nop
80000aa0:	00000013          	nop
80000aa4:	00000013          	nop
