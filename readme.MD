# Processador Simplificado de Ciclo Único ARM

Este repositório contém a implementação de um processador simplificado de ciclo único ARM usando SystemVerilog. O objetivo deste projeto é estender o processador existente, implementar novas instruções e validar seu funcionamento por meio de um programa de teste para a disciplina de arquitetura de computadores do curso de Engenharia de Controle e Automação do Instituto Federal do Espirito Santo (IFES), Campus Serra.

## Instruções Implementadas

O processador de ciclo único ARM implementado neste projeto é capaz de executar as seguintes instruções:

-   **ADD**: realiza uma operação de adição entre dois registradores.
-   **SUB**: realiza uma operação de subtração entre dois registradores.
-   **AND**: realiza uma operação lógica AND bit a bit entre dois registradores.
-   **ORR**: realiza uma operação lógica OR bit a bit entre dois registradores.
-   **LDR**: carrega um valor da memória para um registrador.
-   **STR**: armazena o valor de um registrador na memória.
-   **B**: realiza um desvio condicional para um endereço específico na memória.

## Implementação de Novas Instruções

As modificações exigidas no trabalho consistiram em adicionar as seguintes instruções:

-   **MOV** : A instrução MOV (Move) copia o valor de um registrador para outro registrador. Ela é utilizada para atribuir valores a registradores ou mover dados de um registrador para outro.
-   **CMP**: A instrução CMP (Compare) subtrai dois registradores, definindo as flags de condição com base no resultado da subtração. É frequentemente usada em instruções condicionais para realizar comparações.
-   **TST**: A instrução TST (Test) realiza uma operação lógica AND bit a bit entre dois registradores, atualizando as flags de condição com base no resultado. É usada para testar se um bit específico está definido em um registrador.
-   **EOR**: A instrução EOR (Exclusive OR) executa uma operação lógica XOR bit a bit entre dois registradores, armazenando o resultado em um terceiro registrador. É usada para realizar operações de exclusão lógica.
-   **LDRB**: A instrução LDRB (Load Byte) carrega um byte da memória para um registrador de 32 bits. Ela é útil quando se deseja carregar apenas um byte de um endereço de memória.
-   **STRB**: A instrução STRB (Store Byte) armazena o byte mais baixo de um registrador de 32 bits na memória. Essa instrução é útil para armazenar apenas um byte em um endereço de memória.
-   **BL**: A instrução BL (Branch with Link) realiza um desvio para um endereço específico na memória e armazena o endereço de retorno no registrador de link (LR). É frequentemente usada para chamadas de sub-rotina, permitindo que o fluxo do programa retorne ao ponto de chamada.

## Compilação e Simulação

Após configurar o ambiente de desenvolvimento, siga as etapas abaixo para compilar e simular o projeto:

1. Abra o ambiente de desenvolvimento SystemVerilog.
2. Carregue o projeto do processador simplificado de ciclo único ARM no modelsim.
3. Compile o projeto para verificar se não há erros de sintaxe ou de dependências.
4. Coloque as instruções em hexadecimal no arquivo memfile.dat.
5. Analise os resultados da simulação e verifique se o processador está executando corretamente as instruções implementadas.

## Contato

Caso você tiver alguma dúvida ou sugestão relacionada a este projeto, sinta-se à vontade para entrar em contato com os mantenedores:

-   Nome: Hewerton Folli
-   E-mail: hewerton.fl@gmail.com

-   Nome: Ian Zotelli
-   E-mail: ianzotelli@gmai.com
