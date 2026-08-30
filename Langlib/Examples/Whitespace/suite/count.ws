{Conformance_suite:_count._The_numbers_1_to_10,_one_per_line.}{The_counter_lives_on_the_stack;_`outnum`_prints_a_whole_number,_so}{unlike_brainfuck_there_is_no_decimal_printer_to_write.}{i}[push_1]   	
[label_loop]
  		
[dup] 
 {print_i_(outnum_pops,_so_dup_first)}[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_1]   	
{i_:=_i_+_1}[add]	   [dup] 
 [push_11]   	 		
{i_-_11}[sub]	  	{stop_once_i_has_passed_10}[jz_done]
	 		 
[jump_loop]
 
		
[label_done]
  		 
[drop] 

[halt]


