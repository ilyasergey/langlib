{Conformance_suite:_triangle._Five_rows_of_stars,_row_i_holding_i_of_them.}{Stack_discipline:_the_outer_counter_sits_under_the_inner_one.}{i}[push_1]   	
[label_rows]
  		
{j_:=_i}[dup] 
 [label_stars]
  		 
[dup] 
 {j_=_0:_the_row_is_finished}[jz_starsdone]
	 			
[put_*]   	 	 	 
[outchar]	
  [push_1]   	
{j_:=_j_-_1}[sub]	  	[jump_stars]
 
		 
[label_starsdone]
  			
{discard_the_exhausted_j}[drop] 

[put_LF]   	 	 
[outchar]	
  [push_1]   	
{i_:=_i_+_1}[add]	   [dup] 
 [push_6]   		 
[sub]	  	[jz_done]
	 		  
[jump_rows]
 
		
[label_done]
  		  
[drop] 

[halt]


