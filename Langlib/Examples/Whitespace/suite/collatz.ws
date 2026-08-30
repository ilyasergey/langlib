{Conformance_suite:_collatz._Step_counts_for_1_through_10.}{Heap:_0_=_n,_1_=_v,_2_=_steps._The_inner_loop's_length_is_decided_by}{the_data,_and_the_branch_inside_it_alternates.}[push_0]    
[push_1]   	
[store]		 [label_outer]
  		
[push_1]   	
[push_0]    
[retrieve]			{v_:=_n}[store]		 [push_2]   	 
[push_0]    
{steps_:=_0}[store]		 [label_inner]
  		 
[push_1]   	
[retrieve]			[push_1]   	
[sub]	  	{v_=_1}[jz_innerdone]
	 			
[push_1]   	
[retrieve]			[push_2]   	 
[mod]	 		[jz_even]
	 		  
[push_1]   	
[push_1]   	
[retrieve]			[push_3]   		
[mul]	  
[push_1]   	
[add]	   {v_:=_3v_+_1}[store]		 [jump_bumped]
 
		 	
[label_even]
  		  
[push_1]   	
[push_1]   	
[retrieve]			[push_2]   	 
[div]	 	 {v_:=_v_/_2}[store]		 [label_bumped]
  		 	
[push_2]   	 
[push_2]   	 
[retrieve]			[push_1]   	
[add]	   [store]		 [jump_inner]
 
		 
[label_innerdone]
  			
[push_2]   	 
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   [store]		 [push_0]    
[retrieve]			[push_11]   	 		
[sub]	  	[jz_done]
	 			 
[jump_outer]
 
		
[label_done]
  			 
[halt]


