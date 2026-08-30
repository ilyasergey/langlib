{Conformance_suite:_fib._The_first_twelve_Fibonacci_numbers.}{Heap:_0_=_a,_1_=_b,_2_=_k._Three_cells_updated_in_step,_so_a_botched}{temporary_shows_up_immediately.}[push_0]    
[push_0]    
{a_:=_0}[store]		 [push_1]   	
[push_1]   	
{b_:=_1}[store]		 [push_2]   	 
[push_0]    
{k_:=_0}[store]		 [label_loop]
  		
[push_0]    
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_0]    
[retrieve]			[push_1]   	
[retrieve]			{t_:=_a_+_b,_left_on_the_stack}[add]	   [push_0]    
[push_1]   	
[retrieve]			{a_:=_b}[store]		 [push_1]   	
{store_wants_the_address_under_the_value}[swap] 
	{b_:=_t}[store]		 [push_2]   	 
[push_2]   	 
[retrieve]			[push_1]   	
[add]	   {k_:=_k_+_1}[store]		 [push_2]   	 
[retrieve]			[push_12]   		  
[sub]	  	[jz_done]
	 		 
[jump_loop]
 
		
[label_done]
  		 
[halt]


