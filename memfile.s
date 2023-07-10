mov r2, #3 // R2=3
mov r3, #3 // R3=3
mov r4, #5 // R4=5
tst r2, r3 // 0011 AND 0011 = 0011
tst r2, r4 // 0011 AND 0101 = 0001
cmp r2, r3 // 0011 SUB 0011 = 0000
cmp r2, r4 // 0011 SUB 0101 = -2(2)
eor r5, r2, r3 // 0011 XOR 0011 = 0000
eor r6, r2, r4 // 0011 XOR 0101 = 0110
mov r2,#120 // R2=120
mov r7,#80 // R7=80
str r4, [r2] // R4=5->ENDEREÇO DE MEMÓRIA 30  (120/4=30)
ldrb r0,[r2] //  BYTE CONTEÚDO DO ENDEREÇO DE MEMORIA 30 -> R0
strb r0,[r7] //  R0-> ESCREVE UM BYTE NO ENDEREÇO DE MEMÓRIA 20  (80/4=20)