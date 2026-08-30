{Conformance_suite:_fact._0!_through_7!,_one_per_line.}{Heap:_0_=_n,_1_=_f,_2_=_i._Nested_loops;_5040_is_well_inside}{whitespace's_unbounded_integers.}[push_0]    
[push_0]    
{n_:=_0}[store]		 [label_outer]
  		
[push_1]   	
[push_1]   	
{f_:=_1}[store]		 [push_2]   	 
[push_1]   	
{i_:=_1}[store]		 [label_inner]
  		 
[push_0]    
[retrieve]			[push_2]   	 
[retrieve]			{n_-_i}[sub]	  	{i_has_passed_n}[jn_innerdone]
					
[push_1]   	
[push_1]   	
[retrieve]			[push_2]   	 
[retrieve]			[mul]	  
{f_:=_f_*_i}[store]		 [push_2]   	 
[push_2]   	 
[retrieve]			[push_1]   	
[add]	   {i_:=_i_+_1}[store]		 [jump_inner]
 
		 
[label_innerdone]
  			
[push_1]   	
[retrieve]			[outnum]	
 	[put_LF]   	 	 
[outchar]	
  [push_0]    
[push_0]    
[retrieve]			[push_1]   	
[add]	   {n_:=_n_+_1}[store]		 [push_0]    
[retrieve]			[push_8]   	   
[sub]	  	[jn_outer]
				
[halt]


