import java.util.*;
import soot.jimple.Stmt;
import soot.jimple.AssignStmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.BinopExpr;
import soot.jimple.FieldRef;
import soot.jimple.StaticFieldRef;
import soot.jimple.NegExpr;
import soot.jimple.ConditionExpr;
import soot.jimple.CastExpr;
import soot.Value;
import soot.jimple.Constant;
import soot.Immediate;
import soot.jimple.EqExpr;

import soot.jimple.AddExpr;
import soot.jimple.SubExpr;
import soot.jimple.NeExpr;
import soot.jimple.GtExpr;
import soot.jimple.GeExpr;
import soot.jimple.LeExpr;
import soot.jimple.LtExpr;

public class IAImplementation implements LatticeElement
{
    public HashMap<String,double[]> State= new HashMap<String,double[]>();
	public LatticeElement tf_callstmt(Stmt st)
	{
		 LatticeElement e = new IAImplementation();
		 return e;
	}
    public LatticeElement tf_returnstmt(Stmt st)
	{
		LatticeElement e = new IAImplementation();
		 return e;
	}
    public LatticeElement removeLocalVariables(List<String> globalVariableList)
    {
        LatticeElement e = new IAImplementation();
        for(Map.Entry<String, double[]> iterator : this.State.entrySet())
        {
            String variable = iterator.getKey();
            if(globalVariableList.contains(variable)==true)
            {
                double lowerBound = iterator.getValue()[0];
                double upperBound = iterator.getValue()[1];
                double[] arr = {lowerBound,upperBound};
                ((IAImplementation)e).State.put(variable,arr);
            }
        }
        return e;
    }
	public LatticeElement returnStmt(LatticeElement r, List<String> globalVariableList) //incoming
	{
		LatticeElement e =new IAImplementation();
		 ((IAImplementation)e).State.putAll(this.State);
		int flag=0;
		for(Map.Entry<String,double[]> iterator:this.State.entrySet())
		{
			String variable=iterator.getKey();
			if(globalVariableList.contains(variable)==true && !Double.isNaN(((IAImplementation)r).State.get(variable)[0]))
			{
				 ((IAImplementation)e).State.put(variable, ((IAImplementation)r).State.get(variable));
			}
			if(Double.isNaN(this.State.get(variable)[0]) )
			{
				flag=1;
				break;
			}
			
		}
		double[] bound={Double.NaN,Double.NaN};
		if(flag==1)
		{
			for(Map.Entry<String,double[]> iterator:this.State.entrySet())
			{
				((IAImplementation)e).State.put(iterator.getKey(),bound);
			}
		} 
		return e;
	}
	public LatticeElement join_op(LatticeElement r) 
    {
        LatticeElement e = new IAImplementation();
        for(Map.Entry<String, double[]> iterator : this.State.entrySet())
        {
            String variable = iterator.getKey();
            double lowerBound1 = iterator.getValue()[0];
            double upperBound1 = iterator.getValue()[1];
            double lowerBound2 = ((IAImplementation)r).State.get(variable)[0];
            double upperBound2 = ((IAImplementation)r).State.get(variable)[1];
            double newLowerBound = 0;
            double newUpperBound = 0;

            if(Double.isNaN(lowerBound1) && Double.isNaN(upperBound1))
            {
                if(Double.isNaN(lowerBound2) && Double.isNaN(upperBound2))
                {
                    // bot join bot = bot
                    newLowerBound = Double.NaN; newUpperBound = Double.NaN;
                }
                else
                {
                    // bot join [x,y] = [x,y]
                    newLowerBound = lowerBound2; newUpperBound = upperBound2;
                }
            }
            else if(Double.isNaN(lowerBound2) && Double.isNaN(upperBound2))
            {
                if(Double.isNaN(lowerBound1) && Double.isNaN(upperBound1))
                {
                    // bot join bot = bot
                    newLowerBound = Double.NaN; newUpperBound = Double.NaN;
                }
                else
                {
                    // [x,y] join bot = [x,y]
                    newLowerBound = lowerBound1; newUpperBound = upperBound1;
                }
            }
            else
            {
                // [x1,y1] join [x2,y2]
                newLowerBound = Math.min(lowerBound1,lowerBound2); newUpperBound = Math.max(upperBound1,upperBound2);
            }
            double[] arr = {newLowerBound,newUpperBound};
            ((IAImplementation)e).State.put(variable,arr);
        }
        // return fresh object
    	return e;
    }
	public LatticeElement widen_op(LatticeElement r)
    {
        LatticeElement e = new IAImplementation();
        
        for(Map.Entry<String, double[]> iterator : this.State.entrySet())
        {
            String variable = iterator.getKey();
            double lowerBound1 = iterator.getValue()[0];
            double upperBound1 = iterator.getValue()[1];
            double lowerBound2 = ((IAImplementation)r).State.get(variable)[0];
            double upperBound2 = ((IAImplementation)r).State.get(variable)[1];
            double newLowerBound = 0;
            double newUpperBound = 0;

            if(Double.isNaN(lowerBound1) && Double.isNaN(upperBound1))
            {
                if(Double.isNaN(lowerBound2) && Double.isNaN(upperBound2))
                {
                    // bot widen bot = bot
                    newLowerBound = Double.NaN; newUpperBound = Double.NaN;
                }
                else
                {
                    // bot widen [x,y] = [x,y]
                    newLowerBound = lowerBound2; newUpperBound = upperBound2;
                }
            }
            else if(Double.isNaN(lowerBound2) && Double.isNaN(upperBound2))
            {
                // [x,y] widen bot = [x,y]
                newLowerBound = lowerBound1; newUpperBound = upperBound1;
            }
            else
            {
                // [x1,y1] widen [x2,y2]
                if(lowerBound2 < lowerBound1)
                {
                    newLowerBound = Double.NEGATIVE_INFINITY;
                    if(upperBound2 > upperBound1)
                    {
                        newUpperBound = Double.POSITIVE_INFINITY;
                    }
                    else
                    {
                        newUpperBound = upperBound1;
                    }
                }
                else
                {
                    newLowerBound = lowerBound1;
                    if(upperBound2 > upperBound1)
                    {
                        newUpperBound = Double.POSITIVE_INFINITY;
                    }
                    else
                    {
                        newUpperBound = upperBound1;
                    }
                }
            }
            double[] arr = {newLowerBound,newUpperBound};
            ((IAImplementation)e).State.put(variable,arr);
        }
        // return fresh object
    	return e;
    }
    public boolean equals(LatticeElement r)
    {
        int flag = 0;
        for(Map.Entry<String, double[]> iterator : this.State.entrySet())
        {
            String variable = iterator.getKey();
            double lowerBound1 = iterator.getValue()[0];
            double upperBound1 = iterator.getValue()[1];
            double lowerBound2 = ((IAImplementation)r).State.get(variable)[0];
            double upperBound2 = ((IAImplementation)r).State.get(variable)[1];

            // flag is set if for a variable intervals don't match
			if(!Double.isNaN(lowerBound1) || !Double.isNaN(lowerBound2)){
            if(lowerBound1 != lowerBound2 ){flag=1; break;}
            if(upperBound1 != upperBound2){flag=1; break;}  
			}
		
        }
        if(flag==0) return true;
        else return false;
    }

    public LatticeElement tf_assignstmt(Stmt st) 
    {
    	LatticeElement e = new IAImplementation();
    	// To store all other variable in the new element.
    	((IAImplementation)e).State.putAll(this.State);
    	
    	
        if(st instanceof JAssignStmt)
        {
            JAssignStmt assignmentStatement = (JAssignStmt) st;
            Value leftExpression = assignmentStatement.getLeftOp();
            Value rightExpression = assignmentStatement.getRightOp();
            // Stores interval for the LHS of assignment statement
            double resBound[]=new double[2];
			if(st.containsFieldRef())
			{
				if(!(rightExpression instanceof Constant)) 
                {
				    resBound[0]=this.State.get(rightExpression.toString())[0];
            	    resBound[1]=this.State.get(rightExpression.toString())[1];
				}
			}
            // i=(int) -45;
            if(rightExpression instanceof CastExpr)
            {
            	CastExpr cast=(CastExpr) rightExpression;
            	resBound[0]=Double.parseDouble(cast.getOp().toString());
            	resBound[1]=Double.parseDouble(cast.getOp().toString());
            }
            if(rightExpression instanceof NegExpr)
            {
            	NegExpr ne = (NegExpr) rightExpression;
            
            	double NegativeBound[]= this.State.get(ne.getOp().toString());
            	double tempNeg1=-NegativeBound[0];
            	double tempNeg2=-NegativeBound[1];

            	resBound[0]=Math.min(tempNeg1, tempNeg2);
            	resBound[1]=Math.max(tempNeg1, tempNeg2);
            	
            }
            // x= 10;
            if(rightExpression instanceof Constant)
            {
            	resBound[0]=Double.parseDouble(rightExpression.toString());
            	resBound[1]=Double.parseDouble(rightExpression.toString());
            }
            // x=y;
            else if(rightExpression instanceof Immediate)
            {
            	resBound[0]=this.State.get(rightExpression.toString())[0];
            	resBound[1]=this.State.get(rightExpression.toString())[1];
            }
            // RHS has two operands
            else if(rightExpression instanceof BinopExpr)
            {
                BinopExpr binaryExpression = (BinopExpr) rightExpression;
                Value leftOperand = binaryExpression.getOp1();
                Value rightOperand = binaryExpression.getOp2();
                // Interval of left operand of RHS 
                double leftOpBound[]=new double[2];
                //Interval of right operandd of RHS
                double rightOpBound[]=new double[2];
                
                double temp[]=new double[4];
                
                // x= 1 + operand;
                if(leftOperand instanceof Constant)
                {
                	leftOpBound[0]=Double.parseDouble(leftOperand.toString());
                	leftOpBound[1]=Double.parseDouble(leftOperand.toString());
                }
                 // x= y + operand;
                else
                {   
                	double leftOpBoundtemp[]= this.State.get(leftOperand.toString());
                	// Gets interval for y
                	leftOpBound=leftOpBoundtemp;
                }
                
                // x = operand + 1;
                if(rightOperand instanceof Constant)
                {
                	rightOpBound[0]=Double.parseDouble(rightOperand.toString());
                	rightOpBound[1]=Double.parseDouble(rightOperand.toString());
                }
                // x = operand + y;
                else
                {
                	double rightOpBoundtemp[]= this.State.get(rightOperand.toString());
                	rightOpBound=rightOpBoundtemp;
                }
                
                // If neither operand is bot
                if(!(Double.isNaN(leftOpBound[0]))||(!(Double.isNaN(rightOpBound[0]))))
                {
                	// For addition, interval =[ op1[low]+op2[low], op1[high],op2[high]]
                   	if(binaryExpression instanceof AddExpr)
                	{
            		  
                		resBound[0]=leftOpBound[0]+rightOpBound[0];
                		resBound[1]=leftOpBound[1]+rightOpBound[1];
                	}
            	    else if(binaryExpression instanceof SubExpr)
            	    {
            	    	//Apply operations on 4 combination of bounds
            	    	temp[0]=leftOpBound[0]-rightOpBound[0];
            	    	temp[1]=leftOpBound[0]-rightOpBound[1];
            	    	temp[2]=leftOpBound[1]-rightOpBound[0];
            	    	temp[3]=leftOpBound[1]-rightOpBound[1];
        		      
        		       // Boundary cases
            	    	if(leftOpBound[0]==Double.NEGATIVE_INFINITY&&leftOpBound[0]==Double.NEGATIVE_INFINITY) 
            	    	{
                   	    		temp[0]=Double.NEGATIVE_INFINITY;
            	    	}
            	    	if(leftOpBound[1]==Double.POSITIVE_INFINITY&&leftOpBound[1]==Double.POSITIVE_INFINITY) 
            	    	{
            	    		temp[3]=Double.POSITIVE_INFINITY;
            	    	}
            	    	
            	    	//  take its min and max as interval
            	    	resBound[0]=Math.min(Math.min(temp[0], temp[1]), Math.min(temp[2], temp[3]));
            	    	resBound[1]=Math.max(Math.max(temp[0], temp[1]), Math.max(temp[2], temp[3]));
            	    }
                	//Multiplication 
            	    else
            	    {
            		     temp[0]=leftOpBound[0]*rightOpBound[0];
            		     temp[1]=leftOpBound[0]*rightOpBound[1];
            		     temp[2]=leftOpBound[1]*rightOpBound[0];
            		     temp[3]=leftOpBound[1]*rightOpBound[1];
            		     
            		     
            		     //Boundary Cases infinity * 0
            		      if((leftOpBound[0]==Double.NEGATIVE_INFINITY||rightOpBound[0]==Double.NEGATIVE_INFINITY)&&
            		    		  (leftOpBound[0]==0||rightOpBound[0]==0))
            		      {
            		    	  temp[0]=0;
            		      }
            		      if((leftOpBound[0]==Double.NEGATIVE_INFINITY||rightOpBound[1]==Double.POSITIVE_INFINITY)&&
            		    		  (leftOpBound[0]==0||rightOpBound[1]==0))
            		      {
            		    	  temp[1]=0;
            		      }
            		      if((leftOpBound[1]==Double.POSITIVE_INFINITY||rightOpBound[0]==Double.NEGATIVE_INFINITY)&&
            		    		(  leftOpBound[1]==0||rightOpBound[0]==0))
            		      {
            		    	  temp[2]=0;
            		      }
              		      if((leftOpBound[1]==Double.POSITIVE_INFINITY||rightOpBound[1]==Double.POSITIVE_INFINITY)&&
            		    		  (leftOpBound[1]==0||rightOpBound[1]==0))
              		      {
            		    	  temp[3]=0;
            		      }
            		    	  

            		      resBound[0]=Math.min(Math.min(temp[0], temp[1]), Math.min(temp[2], temp[3]));
            		      resBound[1]=Math.max(Math.max(temp[0], temp[1]), Math.max(temp[2], temp[3]));                		  
                	  
            	   	 }
                 }
                 else
                 {
                	 resBound[0]=Double.NaN;
                	 resBound[1]=Double.NaN;
                 }
             }
             if(resBound[0]==-0)
             {
            	resBound[0]=0;
             }
             if(resBound[1]==-0) 
             {
            	resBound[1]=0;
             }
             
             // Update State Variable
            ((IAImplementation)e).State.put(leftExpression.toString(),resBound);
            
        }
    	return e;
    }

    
    public LatticeElement tf_condstmt(boolean b, Stmt st)
    { 
    	LatticeElement e=new IAImplementation();
    	// To store all other variable in the new element.

        ((IAImplementation)e).State.putAll(this.State); 

    	IfStmt ifStatement = (IfStmt) st;
    	// result Interval
    	double resBound[]=new double[2]; 
    	// left operand
    	double leftOpBound[]= new double[2];
    	//right operand 
    	double rightOpBound[]=new double[2]; 
    	
    	
    	if(ifStatement.getCondition() instanceof BinopExpr) 
    	{
    		BinopExpr binaryExpression = (BinopExpr) ifStatement.getCondition();
    		Value leftOperand=null;
    		Value rightOperand=null;
    		Value tempLeft=binaryExpression.getOp1();
    		Value tempRight = binaryExpression.getOp2();
    		leftOperand=tempLeft;
			rightOperand=tempRight;
			String variable="";
			
			
			if(tempRight instanceof Constant && tempLeft instanceof Constant)
			{
				variable="";
			}
			// Eg x>1
			else if(tempRight instanceof Constant ) 
    		{
				// variable to be changed
    			variable=leftOperand.toString();
    			 // get interval of x
    			leftOpBound= this.State.get(leftOperand.toString());
    			rightOpBound[0]=Double.parseDouble(rightOperand.toString());
            	rightOpBound[1]=Double.parseDouble(rightOperand.toString());
    		}
			// Eg 1 >x
			else if(tempLeft instanceof Constant) 
			{	
				variable=rightOperand.toString();
				// get interval of x
				rightOpBound= this.State.get(rightOperand.toString()); 
    			leftOpBound[0]=Double.parseDouble(leftOperand.toString());
            	leftOpBound[1]=Double.parseDouble(leftOperand.toString());
			}
			// Eg x<y
			else    
			{	
				variable=leftOperand.toString();
				 // get interval of x
    			leftOpBound= this.State.get(leftOperand.toString());
    			 // get interval of y
    			rightOpBound= this.State.get(rightOperand.toString());

    		}
    		
    		if(b== true)
    		{
    			// first operand is variable and  second operand has constant interval or is a constant
    			if((!(leftOperand instanceof Constant)) && (rightOpBound[0]==rightOpBound[1])) 
    			{
    				
    				Double constantVal= rightOpBound[0];
    				if(binaryExpression instanceof EqExpr)
    				{
    					//constant lies within range of x
    					if(constantVal >= leftOpBound[0] && constantVal<= leftOpBound[1]) 
    					{
    						resBound[0]=constantVal;
    						resBound[1]= constantVal;
    					}
    					// if outside range then NaN
    					else 
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				 //x!=10
    				if(binaryExpression instanceof NeExpr)
    				{
    					// x=[10,20]
    					if(leftOpBound[0]==constantVal)  
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=leftOpBound[1];
    					}
    					// x=[1,10]
    					else if(leftOpBound[1]==constantVal) 
    					{
    						resBound[0]= leftOpBound[0];
    						resBound[1]=leftOpBound[1]-1;
    					}
    					// 10 lies within or outside interval of x
    					else  
    					{
    						resBound[0]= leftOpBound[0];
    						resBound[1]=leftOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				// x<= 10
                	if(binaryExpression instanceof LeExpr) 
                	{
                		
                		resBound[0]=leftOpBound[0];
                		// can not exceed constantVal
                		resBound[1] =Math.min(leftOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
                	// x< 10
                	if(binaryExpression instanceof LtExpr) 
                	{
                		resBound[0]=leftOpBound[0];
                		resBound[1] =Math.min(leftOpBound[1], constantVal);
                		// x=[4,15] then x=[4,9] as it is cannot be equal to 10
                		if(resBound[1]==constantVal) 
                			resBound[1]-=1;
                		 // x=[12,15] it must give bot
                		if(resBound[0]> resBound[1])
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
                	 // x>= 10
                	if(binaryExpression instanceof GeExpr)
                	{
                		resBound[1]=leftOpBound[1];
                		resBound[0] =Math.max(leftOpBound[0], constantVal);
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
                	 // x>= 10
                	if(binaryExpression instanceof GtExpr)
                	{
                		resBound[1]=leftOpBound[1];
                		resBound[0] =Math.max(leftOpBound[0], constantVal);
                		// x=[5,15] result x=[11,15] as 10 has to be excluded
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				
    			}
    			// Eg 1 < x
    			else if((leftOperand instanceof Constant) && (!(rightOperand instanceof Constant)))
    			{
    				Double constantVal= leftOpBound[0];
    				if(binaryExpression instanceof EqExpr)
    				{
    					//constant lies within range of x
    					
    					if(constantVal >= rightOpBound[0] && constantVal<= rightOpBound[1]) 
    					{
    						resBound[0]=constantVal;
    						resBound[1]= constantVal;
    					}
    				   // if outside range then NaN
    					else 
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    			    }       			   
    				//x!=10
    				if(binaryExpression instanceof NeExpr) 
    				{
    					// x=[10,20]
    					if(rightOpBound[0]==constantVal)  
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=rightOpBound[1];
    					}
    					// x=[1,10]
    					else if(rightOpBound[1]==constantVal) 
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1]-1;
    					}
    					// 10 within x interval or outside range of x
    					else  
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				// 10<=x
    				if(binaryExpression instanceof LeExpr) 
                	{
                		
    					resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		 // x=[2,5] it must give bot
                		if(resBound[0]> resBound[1])
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
    				// 10<x
    				if(binaryExpression instanceof LtExpr) 
                	{
                		resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>=x
    				if(binaryExpression instanceof GeExpr) 
                	{
                		
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>x
    				if(binaryExpression instanceof GtExpr) 
                	{
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[4,15] then x=[4,9]
                		if(resBound[1]==constantVal) 
                			resBound[1]-=1;
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    			}
    			// Both operands are constants Eg 1==1
        		else if((rightOperand instanceof Constant)&&(leftOperand instanceof Constant))
    			{
        			// If condition fails return bot otherwise Identity
    				if((binaryExpression instanceof EqExpr)&&(!(Integer.parseInt(leftOperand.toString())==Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof NeExpr)&&(!(Integer.parseInt(leftOperand.toString())!=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof GeExpr)&&(!(Integer.parseInt(leftOperand.toString())>=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof GtExpr)&&(!(Integer.parseInt(leftOperand.toString())>Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof LtExpr)&&(!(Integer.parseInt(leftOperand.toString())<Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof LeExpr)&&(!(Integer.parseInt(leftOperand.toString())<=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    					
    			}
    			//y is not a fixed interval it is identity
    			else 
    			{
					if(leftOpBound[0]==leftOpBound[1])
					{
						variable=rightOperand.toString();
						Double constantVal= leftOpBound[0];
    					if(binaryExpression instanceof EqExpr)
    					{
    					//constant lies within range of x
    					
    						if(constantVal >= rightOpBound[0] && constantVal<= rightOpBound[1]) 
    						{
    							resBound[0]=constantVal;
    							resBound[1]= constantVal;
    						}
    				   	// if outside range then NaN
    						else 
    						{
    							resBound[0]=Double.NaN;
    							resBound[1]=Double.NaN;
    						}
    			   	 }       			   
    				//x!=10
    				if(binaryExpression instanceof NeExpr) 
    				{
    					// x=[10,20]
    					if(rightOpBound[0]==constantVal)  
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=rightOpBound[1];
    					}
    					// x=[1,10]
    					else if(rightOpBound[1]==constantVal) 
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1]-1;
    					}
    					// 10 within x interval or outside range of x
    					else  
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				// 10<=x
    				if(binaryExpression instanceof LeExpr) 
                	{
                		
    					resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		 // x=[2,5] it must give bot
                		if(resBound[0]> resBound[1])
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
    				// 10<x
    				if(binaryExpression instanceof LtExpr) 
                	{
                		resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>=x
    				if(binaryExpression instanceof GeExpr) 
                	{
                		
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>x
    				if(binaryExpression instanceof GtExpr) 
                	{
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[4,15] then x=[4,9]
                		if(resBound[1]==constantVal) 
                			resBound[1]-=1;
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}

					}
					else{
    					resBound[0]=leftOpBound[0];
    					resBound[1]=leftOpBound[1];
					}
    			}
    		}
    		// boolean false
    		else
    		{
    			// second operand is constant or has constant interval and left operand is variable
    			if((!(leftOperand instanceof Constant))&&(rightOpBound[0]==rightOpBound[1])) 
    			{
    				Double constantVal= rightOpBound[0];
    				//x==10
    				if(binaryExpression instanceof EqExpr) 
    				{
    					// x=[10,20]
    					if(leftOpBound[0]==constantVal)  
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=leftOpBound[1];
    					}
    					// x=[1,10]
    					else if(leftOpBound[1]==constantVal) 
    					{
    						resBound[0]= leftOpBound[0];
    						resBound[1]=leftOpBound[1]-1;
    					}
    					// 10 within x interval or outside
    					else  
    					{
    						resBound[0]= leftOpBound[0];
    						resBound[1]=leftOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				//x!=10 acts like equal in true
    				if(binaryExpression instanceof NeExpr) 
    				{
    					//constant lies within range
    					if(constantVal >= leftOpBound[0] && constantVal<= leftOpBound[1]) 
    					{
    						resBound[0]=constantVal;
    						resBound[1]= constantVal;
    					}
    					// if outside range then NaN
    					else 
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				// x<= 10 acts like GtExpr for true
                	if(binaryExpression instanceof LeExpr) 
                	{
                		resBound[1]=leftOpBound[1];
                		resBound[0] =Math.max(leftOpBound[0], constantVal);
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		 // x=[2,5] it must give bot
                		if(resBound[0]> resBound[1])
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
                	 // x< 10 acts like GeExpr
                	if(binaryExpression instanceof LtExpr)
                	{
                		resBound[1]=leftOpBound[1];
                		resBound[0] =Math.max(leftOpBound[0], constantVal);
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
                	// x< 10 acts like LtExpr for true
                	if(binaryExpression instanceof GeExpr) 
                	{
                		resBound[0]=leftOpBound[0];
                		resBound[1] =Math.min(leftOpBound[1], constantVal);
                		 // x=[4,15] then x=[4,9]
                		if(resBound[1]==constantVal)
                			resBound[1]-=1;
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
                	 // x< 10 acts like LeExpr for true
                	if(binaryExpression instanceof GtExpr)
                	{
                		resBound[0]=leftOpBound[0];
                		resBound[1] =Math.min(leftOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    			}
    			// rightOperand is variable and left Operand is constant
    			else if((leftOperand instanceof Constant) && (!(rightOperand instanceof Constant)))
    			{
    				Double constantVal= leftOpBound[0];
    				if(binaryExpression instanceof NeExpr)
    				{
    					//constant lies within range
    					if(constantVal >= rightOpBound[0] && constantVal<= rightOpBound[1]) 
    					{
    						resBound[0]=constantVal;
    						resBound[1]= constantVal;
    					}
    					// if outside range then NaN
    					else 
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				//x==10
    				if(binaryExpression instanceof EqExpr) 
    				{
    					 // x=[10,20]
    					if(rightOpBound[0]==constantVal) 
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=rightOpBound[1];
    					}
    					// x=[1,10]
    					else if(rightOpBound[1]==constantVal) 
    					{
    						resBound[0]=rightOpBound[0];
    						resBound[1]=rightOpBound[1]-1;
    					}
    					// 10 within x interval or outside
    					else  
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				 // 10<=x
    				if(binaryExpression instanceof GtExpr)
                	{
                		
    					resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
    				// 10<x
    				if(binaryExpression instanceof GeExpr) 
                	{
                		resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>=x
    				if(binaryExpression instanceof LtExpr) 
                	{
                		
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				 // 10>x
    				if(binaryExpression instanceof LeExpr)
                	{
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[4,15] then x=[4,9]
                		if(resBound[1]==constantVal) 
                			resBound[1]-=1;
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
   				}
    			//Both operands are constant
    			else if((rightOperand instanceof Constant)&&(leftOperand instanceof Constant))
    			{
    				if((binaryExpression instanceof EqExpr)&&((Integer.parseInt(leftOperand.toString())==Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof NeExpr)&&((Integer.parseInt(leftOperand.toString())!=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof GeExpr)&&((Integer.parseInt(leftOperand.toString())>=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof GtExpr)&&((Integer.parseInt(leftOperand.toString())>Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof LtExpr)&&((Integer.parseInt(leftOperand.toString())<Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    				if((binaryExpression instanceof LeExpr)&&((Integer.parseInt(leftOperand.toString())<=Integer.parseInt(rightOperand.toString()))))
    				{
    					resBound[0]=Double.NaN;
    					resBound[1]=Double.NaN;
    				}
    			}
    			//Both operands are variables
    			else
    			{
					if(leftOpBound[0]==leftOpBound[1]){
						variable=rightOperand.toString();
						Double constantVal= leftOpBound[0];
    				if(binaryExpression instanceof NeExpr)
    				{
    					//constant lies within range
    					if(constantVal >= rightOpBound[0] && constantVal<= rightOpBound[1]) 
    					{
    						resBound[0]=constantVal;
    						resBound[1]= constantVal;
    					}
    					// if outside range then NaN
    					else 
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				//x==10
    				if(binaryExpression instanceof EqExpr) 
    				{
    					 // x=[10,20]
    					if(rightOpBound[0]==constantVal) 
    					{
    						resBound[0]=constantVal+1;
    						resBound[1]=rightOpBound[1];
    					}
    					// x=[1,10]
    					else if(rightOpBound[1]==constantVal) 
    					{
    						resBound[0]=rightOpBound[0];
    						resBound[1]=rightOpBound[1]-1;
    					}
    					// 10 within x interval or outside
    					else  
    					{
    						resBound[0]= rightOpBound[0];
    						resBound[1]=rightOpBound[1];

    					}
    					if(resBound[0]>resBound[1])
    					{
    						resBound[0]=Double.NaN;
    						resBound[1]=Double.NaN;
    					}
    				}
    				 // 10<=x
    				if(binaryExpression instanceof GtExpr)
                	{
                		
    					resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}

                	}
    				// 10<x
    				if(binaryExpression instanceof GeExpr) 
                	{
                		resBound[1]=rightOpBound[1];
                		resBound[0] =Math.max(rightOpBound[0], constantVal);
                		if(resBound[0]==constantVal)
                			resBound[0]+=1;
                		// x=[2,5] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				// 10>=x
    				if(binaryExpression instanceof LtExpr) 
                	{
                		
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
    				 // 10>x
    				if(binaryExpression instanceof LeExpr)
                	{
                		resBound[0]=rightOpBound[0];
                		resBound[1] =Math.min(rightOpBound[1], constantVal);
                		// x=[4,15] then x=[4,9]
                		if(resBound[1]==constantVal) 
                			resBound[1]-=1;
                		// x=[12,15] it must give bot
                		if(resBound[0]> resBound[1]) 
                		{
                			resBound[0]=Double.NaN;
                			resBound[1]=Double.NaN;
                		}
                	}
					}
					else{
    				resBound[0]=leftOpBound[0];
    				resBound[1]=leftOpBound[1];
					}
    			}
    		}
    		// For checking
    		if(resBound[0]> resBound[1]) 
    		{
    			resBound[0]=Double.NaN;
    			resBound[1]=Double.NaN;
    		}
    		// If the new value is Bot update all other variables to show bot
    		if(Double.isNaN(resBound[0]))
    		{
    			for(Map.Entry<String, double[]> var:this.State.entrySet())
    			{
    				double value[]= {Double.NaN,Double.NaN};
    				((IAImplementation)e).State.put(var.getKey(), value);
    			}
    		}
    		// when two operands are not constant
    		if(!(variable.equals("")))
    			((IAImplementation)e).State.put(variable.toString(),resBound);

    	}
    return e;
    	
    }

}