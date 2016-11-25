# softwareReliability
aaa:

    SRT :: Part2GivenTests/part2_correct_1.c        // unknown,because of the assume, the while condition isnot assigned
    SRT :: Part2GivenTests/part2_correct_11.c       // unknown, big while condition
    SRT :: Part2GivenTests/part2_correct_12.c       // unknown, it is assume, not assign a variablt 
    SRT :: Part2GivenTests/part2_correct_13.c   !!  // incorrect, problem with bxor  
    SRT :: Part2GivenTests/part2_correct_14.c       // unknown, the while condition is not assigned
    SRT :: Part2GivenTests/part2_correct_17.c       // unknown, whileID->exception->unknown; large loop time->unknown
    SRT :: Part2GivenTests/part2_correct_18.c       // unknown, assume;not assign
    SRT :: Part2GivenTests/part2_correct_19.c       // unknown, for not losing score
    SRT :: Part2GivenTests/part2_correct_2.c        // unknown, assume;not assign
    SRT :: Part2GivenTests/part2_correct_21.c       // pass
    SRT :: Part2GivenTests/part2_correct_22.c       // unknown, while in while
    SRT :: Part2GivenTests/part2_correct_24.c       // unknown, large loop condition
    SRT :: Part2GivenTests/part2_correct_25.c       // unknown, while in while
    SRT :: Part2GivenTests/part2_correct_26.c       // unknown, while inside while
    SRT :: Part2GivenTests/part2_correct_3.c    !!  // incorrect, call 
    SRT :: Part2GivenTests/part2_correct_30.c       // unknown, assume, 
    SRT :: Part2GivenTests/part2_correct_31.c       // unknown, undefined while condition
    SRT :: Part2GivenTests/part2_correct_32.c       // unknown, assume;
    SRT :: Part2GivenTests/part2_correct_33.c       // unknown, assume;
    SRT :: Part2GivenTests/part2_correct_34.c   !!  // incorrect problem with bv2int
    SRT :: Part2GivenTests/part2_correct_38.c       // unknown
    SRT :: Part2GivenTests/part2_correct_43.c       // unknown, while in while
    SRT :: Part2GivenTests/part2_correct_46.c   !!  // incorrect, undefined behaviour
    SRT :: Part2GivenTests/part2_correct_47.c       // unknown, assume,not assign 
    SRT :: Part2GivenTests/part2_correct_49.c       // unknown, time out
    SRT :: Part2GivenTests/part2_correct_5.c        // unknown, too big while times     
    SRT :: Part2GivenTests/part2_correct_50.c       // unknown, assume, not assign
    SRT :: Part2GivenTests/part2_correct_52.c       // unknown, assume, not assign
    SRT :: Part2GivenTests/part2_correct_53.c       // unknown, while in while
    SRT :: Part2GivenTests/part2_correct_54.c       // unknown, assume,  not assing
    SRT :: Part2GivenTests/part2_correct_56.c       // unknown, call->SMT error->unknown
    SRT :: Part2GivenTests/part2_correct_57.c   !!  // incorrect call problem
    SRT :: Part2GivenTests/part2_correct_58.c       // unknown, does not init i and j
    SRT :: Part2GivenTests/part2_correct_59.c       // unknown, large while 
    SRT :: Part2GivenTests/part2_correct_60.c       // unknown, large while and assume
    SRT :: Part2GivenTests/part2_correct_62.c       // unknown, assume ,not assign
    SRT :: Part2GivenTests/part2_correct_63.c       // unknown, large while and assume
    SRT :: Part2GivenTests/part2_correct_8.c    !!  // incorrect, problem with bv2int
    
    ///////////////////////////////////////////////////////////
    SRT :: Part2GivenTests/part2_incorrect_10.c     // UNKNOWN because of time out
    SRT :: Part2GivenTests/part2_incorrect_12.c
    SRT :: Part2GivenTests/part2_incorrect_14.c
    SRT :: Part2GivenTests/part2_incorrect_15.c
    SRT :: Part2GivenTests/part2_incorrect_17.c     // UNKNOW  good luck
    SRT :: Part2GivenTests/part2_incorrect_18.c     // UNKNOW GOOD LUCK; BECAUSE OF DEEP CALL    
    SRT :: Part2GivenTests/part2_incorrect_19.c
    SRT :: Part2GivenTests/part2_incorrect_20.c
    SRT :: Part2GivenTests/part2_incorrect_22.c
    SRT :: Part2GivenTests/part2_incorrect_23.c
    SRT :: Part2GivenTests/part2_incorrect_27.c     // unknow; because of while in while(deepth 5),big unwind level
    SRT :: Part2GivenTests/part2_incorrect_29.c
    SRT :: Part2GivenTests/part2_incorrect_3.c      // pass
    SRT :: Part2GivenTests/part2_incorrect_30.c     // unknown, because of big unwind level
    SRT :: Part2GivenTests/part2_incorrect_33.c     // unknown, because of big unwind level
    SRT :: Part2GivenTests/part2_incorrect_35.c     // unknown, because of big unwind level
    SRT :: Part2GivenTests/part2_incorrect_4.c      // problem with whileID
    SRT :: Part2GivenTests/part2_incorrect_43.c     // pass
    SRT :: Part2GivenTests/part2_incorrect_44.c     // unknown, because of assume a large while condition
    SRT :: Part2GivenTests/part2_incorrect_45.c     // pass
    SRT :: Part2GivenTests/part2_incorrect_47.c     // unknown, because of not assign a variable but assume its range
    SRT :: Part2GivenTests/part2_incorrect_49.c  !! // should be incorrect,but report correct;because of deep call 
    SRT :: Part2GivenTests/part2_incorrect_50.c     // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT;SMT WRONG;WHILE IN WHILE 
    SRT :: Part2GivenTests/part2_incorrect_51.c     // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_52.c     // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_55.c     // unknown, previous correct is just luck
    SRT :: Part2GivenTests/part2_incorrect_56.c     // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_57.c     // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT; while in while
    SRT :: Part2GivenTests/part2_incorrect_7.c      // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT; while in while
    SRT :: Part2GivenTests/part2_incorrect_8.c





    SRT :: Part2GivenTests/part2_correct_60.c
    SRT :: Part2GivenTests/part2_correct_61.c
    SRT :: Part2GivenTests/part2_correct_62.c
    SRT :: Part2GivenTests/part2_correct_63.c
    SRT :: Part2GivenTests/part2_correct_8.c
    SRT :: Part2GivenTests/part2_incorrect_1.c   // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_10.c  // Pass; larger the time limitation 
    SRT :: Part2GivenTests/part2_incorrect_12.c  // UNKNOW or CORRECT; because of time out
    SRT :: Part2GivenTests/part2_incorrect_14.c  // UNKNOW or CORRECT; because of time out
    SRT :: Part2GivenTests/part2_incorrect_15.c  // call
    SRT :: Part2GivenTests/part2_incorrect_19.c  // -1 out of the time limitation
    SRT :: Part2GivenTests/part2_incorrect_20.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT  
    SRT :: Part2GivenTests/part2_incorrect_21.c  // candidate
    SRT :: Part2GivenTests/part2_incorrect_22.c  // candidate 
    SRT :: Part2GivenTests/part2_incorrect_23.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_24.c  // PASS
    SRT :: Part2GivenTests/part2_incorrect_25.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_27.c  // PASS
    SRT :: Part2GivenTests/part2_incorrect_29.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_33.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_36.c  // PASS
    SRT :: Part2GivenTests/part2_incorrect_37.c  // candidate
    SRT :: Part2GivenTests/part2_incorrect_40.c  // call problem 
    SRT :: Part2GivenTests/part2_incorrect_43.c  // UNKNOWN 
    SRT :: Part2GivenTests/part2_incorrect_44.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_47.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_49.c  // deep call
    SRT :: Part2GivenTests/part2_incorrect_50.c  // 0.8 UNKNOW or 0.2*0.8CORRECT or0.2*0.2 INCORRECT;SMT WRONG;WHILE IN WHILE 
    SRT :: Part2GivenTests/part2_incorrect_51.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_52.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_56.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_57.c  // UNKNOW
    SRT :: Part2GivenTests/part2_incorrect_58.c  // 0.8 UNKNOW or 0.2*0.8 CORRECT or 0.2*0.2 INCORRECT
    SRT :: Part2GivenTests/part2_incorrect_7.c   // Passed; change the init unwind depth  from 10 to 4
    SRT :: Part2GivenTests/part2_incorrect_8.c   // unknow; because of time out
    SRT :: Part2GivenTests/part2_incorrect_9.c   // unknow; because of time out
    SRT :: example/Count42.c
