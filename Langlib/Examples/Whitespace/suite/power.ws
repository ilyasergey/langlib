{Conformance_suite:_power._The_powers_of_two_up_to_2^14.}{16384_is_the_widest_value_in_the_suite,_and_whitespace_cells_are}{unbounded_signed_integers,_so_it_needs_nothing_special.}{v}[push_1]   	
[label_loop]
  		
[dup] 
 [outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_2]   	 
{v_:=_v_*_2}[mul]	  
[dup] 
 [push_32768]   	               
[sub]	  	{stop_after_16384_has_been_printed}[jz_done]
	 		 
[jump_loop]
 
		
[label_done]
  		 
[drop] 

[halt]


