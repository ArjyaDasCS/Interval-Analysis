// This program will plot a CFG for a method using soot [ExceptionalUnitGraph feature].
// Arguements : <ProcessOrTargetDirectory> <MainClass> <TargetClass> <TargetMethod>
//Ref: 1) https://gist.github.com/bdqnghi/9d8d990b29caeb4e5157d7df35e083ce
//     2) https://github.com/soot-oss/soot/wiki/Tutorials



////////////////////////////////////////////////////////////////////////////////
import java.util.*;

////////////////////////////////////////////////////////////////////////////////

import soot.options.Options;

import soot.Unit;
import soot.Scene;
import soot.Body;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.Stmt;
import soot.jimple.InvokeExpr;
import soot.jimple.StaticInvokeExpr;
import soot.jimple.AssignStmt;
import soot.jimple.IfStmt;
import soot.jimple.GotoStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.ReturnVoidStmt;
import soot.jimple.DefinitionStmt;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.ExceptionalBlockGraph;
import soot.util.cfgcmd.CFGToDotGraph;
import soot.util.dot.DotGraph;
import soot.UnitPrinter;
import soot.NormalUnitPrinter;

import soot.jimple.BinopExpr;
import soot.jimple.InstanceOfExpr;
import soot.jimple.AddExpr;
import soot.jimple.internal.JIdentityStmt;
import soot.Value;
import soot.jimple.IntConstant;
import soot.jimple.ParameterRef;

import java.io.File;
import java.io.FileWriter;
import java.io.BufferedWriter;
import java.io.PrintWriter;

import soot.SootField;
import soot.Local;
import java.lang.Object.*;
////////////////////////////////////////////////////////////////////////////////



public class Analysis extends PAVBase {
    //private static HashMap<String, Boolean> visited = newHashMap<String, Boolean>();
    private static HashMap<Unit,Boolean> visitedPhase2 = new HashMap<Unit,Boolean>();
    private static ExceptionalUnitGraph graph;
    //private static HashMap<Unit,IAImplementation> ProgramPts = new HashMap<Unit,IAImplementation>();
    private static HashMap<Unit,String> Mapping = new HashMap<Unit,String>();
    private static ArrayList<SootMethod> targetList = new ArrayList<SootMethod>();
    private static HashMap<Unit,HashMap<Unit,IAImplementation>> ProgramPtsGlobal = new HashMap<Unit,HashMap<Unit,IAImplementation>>();
    private static HashMap<Unit,SootMethod> UnitToMethodMapping = new HashMap<Unit,SootMethod>();
    private static List<String> globalVariableList=new ArrayList<String>();
    private static List<SootField> globalVariables=new ArrayList<SootField>();

    // function to extract all global variables in the program
    public void extractGlobalVariables(SootClass targetClass)
    {
        for (SootField field : targetClass.getFields())
        {
            if(field.isStatic())
            {
                globalVariableList.add(field.toString());
                globalVariables.add(field);
            }
        }
    }

    // function to map unit with soot method
    public void UnitToMethodMappingFunction()
    {
        for(SootMethod currentMethod: targetList)
        {
            if (!currentMethod.isPhantom() && currentMethod.isConcrete())
            {
                Body body = currentMethod.retrieveActiveBody();
                for (Unit u : body.getUnits())
                {
                    if (!(u instanceof Stmt))
                    {
                        continue;
                    }
                    UnitToMethodMapping.put(u,currentMethod);
                }
            }
        }
    }

    // function to return method name of a unit
    public static String getMethodNameOfUnit(Unit u)
    {
        String methodName=new String();
        for(Map.Entry<Unit, SootMethod> iterator:UnitToMethodMapping.entrySet())
        {
           if(iterator.getKey()==u)
           {
                methodName=iterator.getValue().getName().toString();
                break;
           }
        }
        return methodName;
    }

    // function to extract local variables of a function and to initialize them with bot
    public static IAImplementation getLocalVariables(SootMethod currentMethod)
    {
        IAImplementation e = new IAImplementation();
        double[] BotBounds= {Double.NaN,Double.NaN};
        if (!currentMethod.isPhantom() && currentMethod.isConcrete())
        {
            Body body = currentMethod.retrieveActiveBody();  
            for (Local local : body.getLocals())
            {
                e.State.put(local.getName(),BotBounds);
            }
            for (Unit u : body.getUnits())
            {
                if (!(u instanceof Stmt))
                {
                    continue;
                }
                Stmt s = (Stmt) u;
                UnitPrinter up = new NormalUnitPrinter(body);
                u.toString(up);

                // for arguments
                if(s instanceof JIdentityStmt)
                {
                    Value rightReference = ((JIdentityStmt) u).getRightOp();
               
                    if(rightReference instanceof ParameterRef)
                    {
                        String parameter = "@parameter";
                        int parameterIndex = (((ParameterRef) rightReference).getIndex());
                        e.State.put(parameter.concat(Integer.toString(parameterIndex)), BotBounds);
                    }
                }
            }      
        }
        return e;
    }

    // function to extract global variables of a function and to initialize them with bot
    public IAImplementation getGlobalVariables(SootClass targetClass)
    {
        IAImplementation e = new IAImplementation();
        double[] BotBounds= {Double.NaN,Double.NaN};
       
        for (SootField field : targetClass.getFields())
        {
            if(field.isStatic())
            {
                e.State.put(field.toString(),BotBounds);
            }
        }
        return e;
    }

    protected static void drawMethodDependenceGraph(SootMethod entryMethod){
        if (!entryMethod.isPhantom() && entryMethod.isConcrete())
        {
            Body body = entryMethod.retrieveActiveBody();
             graph = new ExceptionalUnitGraph(body);

            CFGToDotGraph cfgForMethod = new CFGToDotGraph();
            cfgForMethod.drawCFG(graph);
            DotGraph cfgDot =  cfgForMethod.drawCFG(graph);
            cfgDot.plot("cfg.dot");
        }
    }
   
    // function to attach units with line numbers and to initialize them with bot
    public void AttachandInitialise(SootClass targetClass)
    {
        IAImplementation globalVariableInitialState=getGlobalVariables(targetClass);
        int i=0;
        while(i<targetList.size())
        {
            HashMap<Unit,IAImplementation> callString=new HashMap<Unit,IAImplementation>();
            SootMethod targetMethod= targetList.get(i);
            i++;
            IAImplementation LocalVarInitialState= getLocalVariables(targetMethod);
            IAImplementation mergeVariable=new IAImplementation();
            mergeVariable.State.putAll(globalVariableInitialState.State);
            mergeVariable.State.putAll(LocalVarInitialState.State);
            callString.put(null,mergeVariable);
            if (!targetMethod.isPhantom() && targetMethod.isConcrete() )
            {
              Body body = targetMethod.retrieveActiveBody();
                UnitPrinter up = new NormalUnitPrinter(body);
                int lineNo=0;
                for (Unit u : body.getUnits())
                {
                    if (!(u instanceof Stmt))
                    {
                        continue;
                    }
                    Stmt stmt=(Stmt)u;
                    Mapping.put(u,Integer.toString(lineNo));
                    visitedPhase2.put(u,false);
                    ProgramPtsGlobal.put(u,callString);
                    lineNo++;
                    if (stmt.containsInvokeExpr()  ) {
                       InvokeExpr invokeExpr = stmt.getInvokeExpr();
                       if (invokeExpr instanceof StaticInvokeExpr) {
                            SootMethod method = invokeExpr.getMethod();
                            if(method.getName().equals("random")){
                               continue;
                            }
                            if(targetList.contains(method)==false)
                            targetList.add(method);
                        }
                    }
                }
            }
        }
    }

    // function to check if any variable in the call string table has bot
    public static int checkForBot(IAImplementation e)
    {
        int botFound = 0;
        for(Map.Entry<String,double[]> i:e.State.entrySet())
        {
            double lowerBound = i.getValue()[0];
            double upperBound = i.getValue()[1];
            if(Double.isNaN(lowerBound)==true || Double.isNaN(upperBound)==true)
            {
                botFound = 1;
                break;
            }
        }
        return botFound;
    }

    // function to print output
    public static void printFinalPhase2(SootClass targetClass, SootMethod targetMethod, String targetDirectory, String outputType)
    {
        PAVBase p = new PAVBase();
        Set<ResultTuple> data = new HashSet<ResultTuple>();
        String prefix = targetClass.getName() + ".";
        String inputClassFilePath = targetDirectory;
        for(SootMethod currentMethod: targetList)
        {
            String methodName = currentMethod.getName();
            for(Map.Entry<Unit, SootMethod> iterator:UnitToMethodMapping.entrySet())
            {
                Unit u = iterator.getKey();
                if(iterator.getValue().getName().equals(currentMethod.getName()))
                {
                    String lineNumber = Mapping.get(u);
                    Stmt stmt=(Stmt)u;
                    String programPointNumber = p.getPrgPointName(Integer.valueOf(lineNumber));
                    HashMap<Unit,IAImplementation> callStringTable = ProgramPtsGlobal.get(u);
                    for(Map.Entry<Unit, IAImplementation> it:callStringTable.entrySet())
                    {
                        Unit ut = it.getKey();
                        Stmt st = (Stmt)ut;
                        int botFound = 0;
                        int temp;
                        String var;
                        double lowerBound, upperBound;
                        String lb, ub;
                        String callString;
                        if(ut == null)
                        {
                            callString = "@";
                        }
                        else
                        {
                            callString = p.getPrgPointName(Integer.valueOf(Mapping.get(ut).toString()));
                            callString = prefix + getMethodNameOfUnit(ut) + "." + callString;
                        }
                        for(Map.Entry<String,double[]> i:it.getValue().State.entrySet())
                        {
                            if(callString.equals("@") && (currentMethod.getName().equals(targetMethod.getName())==false))
                            {
                                break;

                            }
                            int BotInCallString = checkForBot(it.getValue());
                            if(BotInCallString == 1)
                            {
                                break;
                            }
                            var = i.getKey();
                            if(globalVariableList.contains(var))
                            {
                                for(int k=0; k<globalVariables.size(); k++)
                                {
                                    if(globalVariables.get(k).toString().equals(var))
                                    {
                                        var = targetClass.getName()+ "." + globalVariables.get(k).getName();
                                    }
                                }
                            }

                            lowerBound = i.getValue()[0];
                            upperBound = i.getValue()[1];
                            if(Double.isNaN(lowerBound) && Double.isNaN(upperBound))
                                {botFound=1;break;}
                            lb = Double.toString(lowerBound);
                            ub = Double.toString(upperBound);
                            if(lb.equals("-Infinity"))
                            {   lb = "-inf";
                            }
                            else
                            {   temp = (int) lowerBound; lb = String.valueOf(temp);
                            }
                            if(ub.equals("Infinity"))
                            {   ub = "+inf";
                            }
                            else
                            {   temp = (int) upperBound; ub = String.valueOf(temp);
                            }
                            ResultTuple tup = new ResultTuple(methodName,programPointNumber,var,lb,ub,callString);
                            data.add(tup);
                        }
                    }
                }
            }
        }
        String[] result = p.fmtOutputData(data,prefix);
        Arrays.sort(result);
        if(outputType.equals("finalOutput"))
        {
            String outputFileName = inputClassFilePath + "/" + targetClass.getName() + "." + targetMethod.getName() + "." + "output.txt";
            File File1 = new File(outputFileName);
            try
            {
                if(File1.exists()==false)
                {
                    File1.createNewFile();
                }
                BufferedWriter writer = new BufferedWriter(new FileWriter(outputFileName));
                for(int j=0; j<result.length; j++)
                {
                    writer.write(result[j]+"\n");
                }
                writer.close();
            }
            catch(Exception e){}
        }
        else if(outputType.equals("intermediate"))
        {
            String outputFileName = inputClassFilePath + "/" + targetClass.getName() + "." + targetMethod.getName() + "." + "fulloutput.txt";
            File File2 = new File(outputFileName);
            try
            {
                if(File2.exists()==false)
                {
                    File2.createNewFile();
                }
                PrintWriter writer = new PrintWriter(new FileWriter(File2, true));
                for(int j=0; j<result.length; j++)
                {
                    writer.write(result[j]+"\n");
                }
                writer.close();
            }
            catch(Exception e){}
        }    
    }

    // function to handle the initial state for target method
    public HashMap<Unit,IAImplementation> InitialStateTargetMethod(SootMethod targetMethod)
    {
        HashMap<Unit,IAImplementation> callString=new HashMap<Unit,IAImplementation>();
        IAImplementation Variables=getLocalVariables(targetMethod);
        double bound[]={Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY};
        for(Map.Entry<String,double[]> it:Variables.State.entrySet())
        {
           
            Variables.State.put(it.getKey(),bound);
        }
        for(String it: globalVariableList){
            Variables.State.put(it,bound);
        }
        callString.put(null,Variables);
        return callString;
    }

    // function to handle the initial state for the called methods
    public static Unit InitialStateHandler(SootMethod calledMethod,Unit callingUnit,HashMap<Unit,IAImplementation> incomingCallString) //Call string has global
    {
        Unit unit=null;  
        for(Map.Entry<Unit,SootMethod> iterator:UnitToMethodMapping.entrySet())
        {
            if((iterator.getValue()).getName().equals(calledMethod.getName()) && (Mapping.get(iterator.getKey()).equals("0")))
            {
                unit= iterator.getKey();
            }
        }
        IAImplementation initialPoint=new IAImplementation();
        IAImplementation nonInitialPoint=new IAImplementation();
        double[] bounds={Double.NEGATIVE_INFINITY,Double.POSITIVE_INFINITY};
        double[] botBounds={Double.NaN,Double.NaN};
        Body body = calledMethod.retrieveActiveBody();  
        for (Local local : body.getLocals())
        {
            initialPoint.State.put(local.getName(),bounds);
            nonInitialPoint.State.put(local.getName(),botBounds);
        }
        HashMap<Unit,IAImplementation> callStringAtPoint= new HashMap<Unit,IAImplementation>();
        HashMap<Unit,IAImplementation> newCallStringAtPoint= new HashMap<Unit,IAImplementation>();
        callStringAtPoint=ProgramPtsGlobal.get(unit);
        for(Map.Entry<Unit,IAImplementation> it: callStringAtPoint.entrySet())
        {
            IAImplementation temp=new IAImplementation();
            temp.State.putAll(it.getValue().State);
            temp.State.putAll(initialPoint.State);
            newCallStringAtPoint.put(it.getKey(),temp);
        }
        ProgramPtsGlobal.put(unit,newCallStringAtPoint);
        IAImplementation newValuesIncoming=new IAImplementation();
        Map.Entry<Unit,IAImplementation> entry = incomingCallString.entrySet().iterator().next();
        newValuesIncoming=(entry.getValue());
        for(Map.Entry<Unit,IAImplementation> it:incomingCallString.entrySet())
        {
            IAImplementation existingValuesIncoming=it.getValue();
            newValuesIncoming=(IAImplementation)newValuesIncoming.join_op(existingValuesIncoming);
        }
        HashMap<Unit,IAImplementation> existingCallString= new HashMap<Unit,IAImplementation>();
        HashMap<Unit,IAImplementation> oldCallString=new HashMap<Unit,IAImplementation>();
        oldCallString=ProgramPtsGlobal.get(unit);
        existingCallString=ProgramPtsGlobal.get(unit);
        HashMap<Unit,IAImplementation> newCallString= new HashMap<Unit,IAImplementation>();
        newCallString.putAll(existingCallString);
        IAImplementation localVariable=getLocalVariables(calledMethod);
        for(Map.Entry<String,double[]> tt:localVariable.State.entrySet())
        {
            localVariable.State.put(tt.getKey(),bounds);
        }
        newValuesIncoming.State.putAll(localVariable.State);      
        IAImplementation temp5=new IAImplementation();
        if(newCallString.containsKey(callingUnit))
        {
            temp5=existingCallString.get(callingUnit);
            IAImplementation newTemp2=(IAImplementation)temp5.widen_op(newValuesIncoming);
            newCallString.put(callingUnit,newTemp2);
            ProgramPtsGlobal.put(unit,newCallString);
        }
        existingCallString=ProgramPtsGlobal.get(unit);
        if(existingCallString.containsKey(callingUnit))
        {
            IAImplementation temp1=new IAImplementation();
            IAImplementation newTemp=new IAImplementation();
            temp1= existingCallString.get(callingUnit);
            newTemp=(IAImplementation)temp1.join_op(newValuesIncoming);
            newCallString.put(callingUnit,newTemp);
        }
        else
        {
            newCallString.put(callingUnit,newValuesIncoming);
        }
        ProgramPtsGlobal.put(unit,newCallString);
        Boolean bool= eqCallString(oldCallString,newCallString);
        if(bool==false)
            visitedPhase2.put(unit,false);
        if(bool==false)
        {
            for(Map.Entry<Unit,SootMethod> iterator:UnitToMethodMapping.entrySet())
            {
                if((iterator.getValue()).getName().equals(calledMethod.getName()) && (!Mapping.get(iterator.getKey()).equals("0")))
                {
                    Unit nonInitialUnits=iterator.getKey();
                    HashMap<Unit,IAImplementation> callStringNonInitial= new HashMap<Unit,IAImplementation>();
                    HashMap<Unit,IAImplementation> newCallStringNonInitial= new HashMap<Unit,IAImplementation>();
                    callStringNonInitial=ProgramPtsGlobal.get(nonInitialUnits);
                    for(Map.Entry<Unit,IAImplementation> it: callStringNonInitial.entrySet())
                    {
                        IAImplementation temp=new IAImplementation();
                        temp.State.putAll(it.getValue().State);
                        temp.State.putAll(nonInitialPoint.State);
                        newCallStringNonInitial.put(it.getKey(),temp);
                    }
                    ProgramPtsGlobal.put(nonInitialUnits,newCallStringNonInitial);
                }
            }
        }
        return unit;
    }

    // function to handle call strings while executing assignment statement
   public static HashMap<Unit,IAImplementation> assignmentCallString(HashMap<Unit,IAImplementation> existing,Stmt st)
    {
        HashMap<Unit,IAImplementation> newCallString=new HashMap<Unit,IAImplementation>();
        for(Map.Entry<Unit,IAImplementation> it: existing.entrySet())
        {
            IAImplementation newValue=(IAImplementation)((it.getValue()).tf_assignstmt(st));
            newCallString.put(it.getKey(),newValue);
        }
        return newCallString;
    }

    // function to check dominance
    public static boolean eqCallString(HashMap<Unit,IAImplementation> existing,HashMap<Unit,IAImplementation> modified)
    {
        boolean bool=false;
        for(Map.Entry<Unit,IAImplementation> it: existing.entrySet())
        {
            if(modified.containsKey(it.getKey()))
            {
                bool=(it.getValue()).equals(modified.get(it.getKey()));
            }
            else
                return false;
            if(bool==false)
                return false;
        }
        if(existing.size()!=modified.size())
            bool=false;
        return bool;
    }

    // function to handle call strings while executing the condition statements
    public HashMap<Unit,IAImplementation> condCallString(HashMap<Unit,IAImplementation> existing,Stmt st,Boolean bool)
    {
        HashMap<Unit,IAImplementation> newCallString=new HashMap<Unit,IAImplementation>();
        for(Map.Entry<Unit,IAImplementation> it: existing.entrySet())
        {
            IAImplementation newValue=(IAImplementation)((it.getValue()).tf_condstmt(bool,st));
            newCallString.put(it.getKey(),newValue);
        }
        return newCallString;
    }
   
    // function to handle call strings while executing join operation
    public HashMap<Unit,IAImplementation> joinCallString(HashMap<Unit,IAImplementation> existing,HashMap<Unit,IAImplementation> incoming)
    {
        HashMap<Unit,IAImplementation> newCallString=new HashMap<Unit,IAImplementation>();
        newCallString.putAll(existing);
        for(Map.Entry<Unit,IAImplementation> it:incoming.entrySet())
        {
            if(newCallString.containsKey(it.getKey()))
            {
                IAImplementation newValue=(IAImplementation)((newCallString.get(it.getKey())).join_op(it.getValue()));
                newCallString.put((it.getKey()),newValue);
            }
            else
            {
                newCallString.put(it.getKey(),it.getValue());
            }
        }
        return newCallString;
    }

    // function to handle call strings while executing widen operation
    public HashMap<Unit,IAImplementation> widenCallString(HashMap<Unit,IAImplementation> existing,HashMap<Unit,IAImplementation> incoming)
    {
        HashMap<Unit,IAImplementation> newCallString=new HashMap<Unit,IAImplementation>();
        newCallString.putAll(existing);
        for(Map.Entry<Unit,IAImplementation> it:incoming.entrySet())
        {
            if(newCallString.containsKey(it.getKey()))
            {
                IAImplementation newValue=(IAImplementation)((newCallString.get(it.getKey())).widen_op(it.getValue()));
                newCallString.put((it.getKey()),newValue);
            }
            else
            {
                newCallString.put(it.getKey(),it.getValue());
            }
        }
        return newCallString;
    }

    // function to return first statment of a method
    public static Unit getFirstUnitOfReturnMethod(SootMethod method)
    {
        for(Map.Entry<Unit,String> iterator: Mapping.entrySet())
        {
            Unit u = iterator.getKey();
            String lineNumber = iterator.getValue();
            if(getMethodNameOfUnit(u).equals(method.getName()) && lineNumber.equals("0"))
            {
                return u;
            }
        }
        return null;   
    }

    // function to handle call strings while executing return statement
    public static void performOperation(Unit x, Unit y)
    {
        // X : First Unit of return method, Y: Return Site Successor
        HashMap<Unit,IAImplementation> callStringTableX = new  HashMap<Unit,IAImplementation>();
        HashMap<Unit,IAImplementation> callStringTableY = new  HashMap<Unit,IAImplementation>();

        callStringTableX = ProgramPtsGlobal.get(x);
        callStringTableY = ProgramPtsGlobal.get(y);

        Boolean compareUnits = callStringTableX.keySet().equals(callStringTableY.keySet());
        if(compareUnits == true)
        {
            // list containing units which has bots at return site successor
            List<Unit> unitsContainingBot = new ArrayList<Unit>();
            List<Unit> unitsNonBot = new ArrayList<Unit>();
            for(Map.Entry<Unit,IAImplementation> iterator:callStringTableY.entrySet())
            {
                Unit yUnit = iterator.getKey();
                if(yUnit != null)
                {
                    int botFound = checkForBot(iterator.getValue());
                    if(botFound == 1)
                    {
                        unitsContainingBot.add(yUnit);
                    }
                    else 
                    {
                        unitsNonBot.add(yUnit);
                    }     
                }
            }
            int size = unitsNonBot.size();
            IAImplementation e = new IAImplementation();
            if(size >= 1)
            {
                e = callStringTableY.get(unitsNonBot.get(0));
                for(int j=1; j<size; j++)
                {
                    IAImplementation f = new IAImplementation();
                    f = callStringTableY.get(unitsNonBot.get(j));
                    e = (IAImplementation)e.join_op(f);
                }
                for(int k=0; k<unitsContainingBot.size(); k++)
                {
                    IAImplementation e2 = new IAImplementation();
                    e2 = callStringTableY.get(unitsContainingBot.get(k));
                    e2.State.putAll(e.State);
                }
            }
        }
        else if(compareUnits == false)
        {
            List<Unit> unitsOfX = new ArrayList<Unit>(callStringTableX.keySet());
            List<Unit> unitsOfY = new ArrayList<Unit>(callStringTableY.keySet());
            List<Unit> unitsToBeAddedToY = new ArrayList<Unit>();
            for(int a=0; a<unitsOfX.size(); a++)
            {
                if(unitsOfX.get(a)!=null)
                {
                    if(unitsOfY.contains(unitsOfX.get(a)) == false)
                    {
                        unitsToBeAddedToY.add(unitsOfX.get(a));
                    }
                }
            }

            List<Unit> unitsContainingBotInY = new ArrayList<Unit>();
            List<Unit> unitsNonBotInY = new ArrayList<Unit>();
            for(Map.Entry<Unit,IAImplementation> iterator:callStringTableY.entrySet())
            {
                Unit yUnit = iterator.getKey();
                if(yUnit != null)
                {
                    int botFound = checkForBot(iterator.getValue());
                    if(botFound == 1)
                    {
                        unitsContainingBotInY.add(yUnit);
                    }
                    else 
                    {
                        unitsNonBotInY.add(yUnit);
                    }     
                }
            }
            int sizeNonBotY = unitsNonBotInY.size();
            IAImplementation e = new IAImplementation();
            if(sizeNonBotY >= 1)
            {
                e = callStringTableY.get(unitsNonBotInY.get(0));
                for(int j=1; j<sizeNonBotY; j++)
                {
                    IAImplementation f = new IAImplementation();
                    f = callStringTableY.get(unitsNonBotInY.get(j));
                    e = (IAImplementation)e.join_op(f);
                }
                for(int k=0; k<unitsContainingBotInY.size(); k++)
                {
                    IAImplementation e2 = new IAImplementation();
                    e2 = callStringTableY.get(unitsContainingBotInY.get(k));
                    e2.State.putAll(e.State);
                }
            }
            int sizeOfList = unitsToBeAddedToY.size();
            IAImplementation m = new IAImplementation();
            if(sizeOfList >= 1)
            {
                for(int k=0; k<unitsToBeAddedToY.size(); k++)
                {
                    IAImplementation e2 = new IAImplementation();
                    e2 = callStringTableX.get(unitsToBeAddedToY.get(k));
                    e2.State.putAll(e.State);
                }
            }
        }
    }

    // Kildall
    public void doAnalysisPhase2(SootMethod targetMethod, SootClass targetClass, String targetDirectory)
    {
        /*************************************************************
         * XXX you can implement your analysis here
         ************************************************************/

        // delete the files (where output has to be written) if already exists
        this.DeleteFilesIfExists(targetClass, targetMethod, targetDirectory);

        HashMap<Unit,IAImplementation> callString=new HashMap<Unit,IAImplementation>();
        callString=InitialStateTargetMethod(targetMethod);
        Unit u=InitialStateHandler(targetMethod,null,callString);
       
        printFinalPhase2(targetClass,targetMethod,targetDirectory,"intermediate");

        while(visitedPhase2.containsValue(false))
        {
            Unit unit=null;
            IAImplementation newValue= new IAImplementation();
            HashMap<Unit,IAImplementation> newCallString=new HashMap<Unit,IAImplementation>();
    
            for(Map.Entry<Unit, Boolean> iterator:visitedPhase2.entrySet())
            {
                if(iterator.getValue()==false) 
                {
                    unit=iterator.getKey();
                    break;
                }
            }
            visitedPhase2.put(unit,true);
            Stmt stmt=(Stmt)unit;
     
            // If ifstatement call conditional method
            if(stmt instanceof IfStmt)
            {
                IfStmt ifstatement=(IfStmt)stmt;

                // gets true branch
                drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                Stmt trueBranch=ifstatement.getTarget();
                for(Unit succ: graph.getSuccsOf(stmt))
                {
                    Stmt successor=(Stmt) succ;

                    // set boolean true for true branch
                    if(succ==trueBranch)
                    {
                        newCallString=condCallString(ProgramPtsGlobal.get(unit),stmt,true);
                    }
                    else
                    {
                        newCallString=condCallString(ProgramPtsGlobal.get(unit),stmt,false);
                    }
        
   
                    // Finds if there is a back-edge. Predecessor size > 1 and predecessor line no > node line number
                    drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                    int PredSize=graph.getPredsOf(succ).size();
                    int headerLineNumber=Integer.parseInt(Mapping.get(succ));
                    HashMap<Unit,IAImplementation> oldCallStringAtSucc=ProgramPtsGlobal.get(succ);
                    if(PredSize>1)
                    {
                        for(Unit pred: graph.getPredsOf(succ))
                        {
                            int PredLineNumber=Integer.parseInt(Mapping.get(pred));
                            if(PredLineNumber> headerLineNumber)
                            {
                                HashMap<Unit,IAImplementation> newCallStringAtSucc=new HashMap<Unit,IAImplementation>();
                                newCallStringAtSucc=widenCallString(oldCallStringAtSucc,newCallString);
                                ProgramPtsGlobal.put(succ,newCallStringAtSucc);                 
                                continue; 
                            }
                        }
                    }
                    HashMap<Unit,IAImplementation> tempCallString=new HashMap<Unit,IAImplementation>();
                    HashMap<Unit,IAImplementation> CallStringAtSucc=new HashMap<Unit,IAImplementation>();
                    tempCallString=ProgramPtsGlobal.get(succ);
                    CallStringAtSucc= joinCallString(tempCallString,newCallString);
                    ProgramPtsGlobal.put(succ,CallStringAtSucc);
                    if((eqCallString(CallStringAtSucc,oldCallStringAtSucc))==false)
                        visitedPhase2.put(succ,false);
                }
            }

            // for any non-if statements
            else
            {   
                if(stmt.containsInvokeExpr())
                {
                    InvokeExpr invokeExpr = stmt.getInvokeExpr();
                    if(invokeExpr instanceof StaticInvokeExpr) 
                    {
                        SootMethod method = invokeExpr.getMethod();
                        if(method.getName().equals("random"))
                        {
                            newCallString=ProgramPtsGlobal.get(unit);
                            drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                            for(Unit succ: graph.getSuccsOf(stmt))
                            {
                                if(eqCallString(newCallString,ProgramPtsGlobal.get(succ))==false)
                                    visitedPhase2.put(succ,false);
                                ProgramPtsGlobal.put(succ,newCallString);
                                 
                            }
                        }
                        else
                        {
                            HashMap<Unit,IAImplementation> CallStringAtCallSite=new HashMap<Unit,IAImplementation>();
                            HashMap<Unit,IAImplementation> transferredCallString=new HashMap<Unit,IAImplementation>();
                            CallStringAtCallSite=ProgramPtsGlobal.get(unit);
                            HashMap<Unit,IAImplementation> succCallString=new HashMap<Unit,IAImplementation>();
                            IAImplementation tempGlobal=getGlobalVariables(targetClass);
                            for(Map.Entry<Unit,IAImplementation> it: CallStringAtCallSite.entrySet())
                            {
                                IAImplementation localVariables= new IAImplementation();
                                localVariables.State.putAll(it.getValue().State);
                                localVariables.State.putAll(tempGlobal.State);
                                newCallString.put(it.getKey(),localVariables);
                            }
                            for(Map.Entry<Unit,IAImplementation> it:CallStringAtCallSite.entrySet())
                            {
                                IAImplementation existingVariables= it.getValue();
                                IAImplementation newVariables= (IAImplementation)existingVariables.removeLocalVariables(globalVariableList);
                                transferredCallString.put(it.getKey(),newVariables);
                            }
                            Unit succFunction=InitialStateHandler(method,unit,transferredCallString);
                            drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                            List<Unit> succ1= graph.getSuccsOf(stmt);
                        }
                    }
                }
                else if(stmt instanceof AssignStmt)
                {
                    newCallString=assignmentCallString(ProgramPtsGlobal.get(unit),stmt);
                }
                else if(stmt instanceof JIdentityStmt)
                {    
                    newCallString=ProgramPtsGlobal.get(unit);
                }
                else if(stmt instanceof GotoStmt)
                {
                    newCallString=ProgramPtsGlobal.get(unit);
                }
                else if(stmt instanceof ReturnVoidStmt)
                {
                    if(getMethodNameOfUnit(unit).equals(targetMethod.getName()))
                    {
                        newCallString=ProgramPtsGlobal.get(unit);
                    }
                    else
                    {
                        HashMap<Unit,IAImplementation> CallStringAtReturnSite=new HashMap<Unit,IAImplementation>();
                        CallStringAtReturnSite=ProgramPtsGlobal.get(unit);
                        HashMap<Unit,IAImplementation> transferredCallString=new HashMap<Unit,IAImplementation>();
                        for(Map.Entry<Unit,IAImplementation> it:CallStringAtReturnSite.entrySet())
                        {
                            IAImplementation existingVariables= it.getValue();          
                            IAImplementation newVariables= (IAImplementation)existingVariables.removeLocalVariables(globalVariableList);
                            transferredCallString.put(it.getKey(),newVariables);
                        }
                        for(Map.Entry<Unit,IAImplementation> it:transferredCallString.entrySet())
                        {
                            Unit returnSite=it.getKey();
                            if(returnSite!=null)
                            {
                                IAImplementation Values=it.getValue();
                                SootMethod returnMethod=UnitToMethodMapping.get(returnSite);
                                IAImplementation temp=getLocalVariables(returnMethod);
                                Values.State.putAll(temp.State);
                                drawMethodDependenceGraph(returnMethod);
                                List<Unit> returnSiteSucc=graph.getSuccsOf(returnSite);
                                HashMap<Unit,IAImplementation> callStringAtReturnSiteSucc=new HashMap<Unit,IAImplementation>();
                                HashMap<Unit,IAImplementation> newCallStringAtReturnSiteSucc=new HashMap<Unit,IAImplementation>();
                                for(int j=0; j<returnSiteSucc.size(); j++)
                                {
                                    callStringAtReturnSiteSucc=ProgramPtsGlobal.get(returnSiteSucc.get(j));
                                    for(Map.Entry<Unit,IAImplementation> it1:callStringAtReturnSiteSucc.entrySet())
                                    {
                                        IAImplementation temp1=it1.getValue();
                                        IAImplementation newValueTemp=(IAImplementation)temp1.join_op(Values);
                                        newCallStringAtReturnSiteSucc.put(it1.getKey(),newValueTemp);
                                    }
                                    ProgramPtsGlobal.put(returnSiteSucc.get(j),newCallStringAtReturnSiteSucc);

                                    // new code here
                                    Unit firstUnitOfReturnMethod = getFirstUnitOfReturnMethod(returnMethod);
                                    performOperation(firstUnitOfReturnMethod, returnSiteSucc.get(j));

                                    if((eqCallString(newCallStringAtReturnSiteSucc,callStringAtReturnSiteSucc))==false)
                                        visitedPhase2.put(returnSiteSucc.get(j),false);
                                }
                            }
                        }
                    }              

                }
                else
                {
                    newCallString=ProgramPtsGlobal.get(unit);
                }
                if((!(stmt instanceof ReturnVoidStmt)) )
                {
                    drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                    for(Unit succ: graph.getSuccsOf(stmt))
                    {
                        HashMap<Unit,IAImplementation> tempCallString=new HashMap<Unit,IAImplementation>();
                        HashMap<Unit,IAImplementation> CallStringAtSucc=new HashMap<Unit,IAImplementation>();
                        tempCallString=ProgramPtsGlobal.get(succ);
                        drawMethodDependenceGraph(UnitToMethodMapping.get(unit));
                        int PredSize=graph.getPredsOf(succ).size();
                        int headerLineNumber=Integer.parseInt(Mapping.get(succ));
                        HashMap<Unit,IAImplementation> oldCallStringAtSucc=ProgramPtsGlobal.get(succ);
                        if(PredSize>1)
                        {
                            for(Unit pred: graph.getPredsOf(succ))
                            {
                                int PredLineNumber=Integer.parseInt(Mapping.get(pred));
                                if(PredLineNumber> headerLineNumber)
                                {
                                
                                    HashMap<Unit,IAImplementation> newCallStringAtSucc=new HashMap<Unit,IAImplementation>();
                                    newCallStringAtSucc=widenCallString(oldCallStringAtSucc,newCallString);
                                    ProgramPtsGlobal.put(succ,newCallStringAtSucc);
                                    continue; 
                                }
                            }
                        }
                        HashMap<Unit,IAImplementation> tempCallString1=new HashMap<Unit,IAImplementation>();
                        HashMap<Unit,IAImplementation> CallStringAtSucc1=new HashMap<Unit,IAImplementation>();
                        tempCallString1=ProgramPtsGlobal.get(succ);
                        CallStringAtSucc1= joinCallString(tempCallString1,newCallString);
                        ProgramPtsGlobal.put(succ,CallStringAtSucc1);
                        if((eqCallString(CallStringAtSucc1,oldCallStringAtSucc))==false)
                            visitedPhase2.put(succ,false);
                    }
                }
        
            }
            printFinalPhase2(targetClass,targetMethod,targetDirectory,"intermediate");
        }
        printFinalPhase2(targetClass,targetMethod,targetDirectory,"finalOutput");
    }

    // function to delete output file if already exists
    public void DeleteFilesIfExists(SootClass targetClass, SootMethod targetMethod, String targetDirectory)
    {
        String outputFileName = targetDirectory + "/" + targetClass.getName() + "." + targetMethod.getName() + "." + "output.txt";
        File File1 = new File(outputFileName);
        try
        {
            if(File1.exists())
            {
                File1.delete();
            }
        }
        catch(Exception e){}
        outputFileName = targetDirectory+ "/" + targetClass.getName() + "." + targetMethod.getName() + "." + "fulloutput.txt";
        File File2 = new File(outputFileName);
        try
        {
            if(File2.exists())
            {
                File2.delete();
            }
        }
        catch(Exception e){}
    }

    public static void main(String[] args)
    {
        //String targetDirectory="./target";
        //String mClass="AddNumFun";
        //String tClass="AddNumFun";
        //String tMethod="expr";
       
        String targetDirectory=args[0];
        String mClass=args[1];
        String tClass=args[2];
        String tMethod=args[3];
        boolean methodFound=false;


        List<String> procDir = new ArrayList<String>();
        procDir.add(targetDirectory);

        // Set Soot options
        soot.G.reset();
        Options.v().set_process_dir(procDir);
        // Options.v().set_prepend_classpath(true);
        Options.v().set_src_prec(Options.src_prec_only_class);
        Options.v().set_whole_program(true);
        Options.v().set_allow_phantom_refs(true);
        Options.v().set_output_format(Options.output_format_none);
        Options.v().set_keep_line_number(true);
        Options.v().setPhaseOption("cg.spark", "verbose:false");

        Scene.v().loadNecessaryClasses();
        SootClass entryClass = Scene.v().getSootClassUnsafe(mClass);
        SootMethod entryMethod = entryClass.getMethodByNameUnsafe("main");
        SootClass targetClass = Scene.v().getSootClassUnsafe(tClass);
        SootMethod targetMethod = entryClass.getMethodByNameUnsafe(tMethod);

        Options.v().set_main_class(mClass);
        Scene.v().setEntryPoints(Collections.singletonList(entryMethod));

        System.out.println (entryClass.getName());
        System.out.println (entryMethod);
        System.out.println("tclass: " + targetClass);
        System.out.println("tmethod: " + targetMethod);
        System.out.println("tmethodname: " + tMethod);
        Iterator mi = targetClass.getMethods().iterator();
        while (mi.hasNext()) {
            SootMethod sm = (SootMethod)mi.next();
            // System.out.println("method: " + sm);
            if(sm.getName().equals(tMethod))
            {methodFound=true; break;}
        }

        if(methodFound) {
            printInfo(targetMethod);
            Analysis a =new Analysis();
            targetList.add(targetMethod);
            a.extractGlobalVariables(targetClass);
            a.AttachandInitialise(targetClass);
            a.UnitToMethodMappingFunction();
            a.doAnalysisPhase2(targetMethod,targetClass,targetDirectory);
    
            /*************************************************************
             * XXX This would be a good place to call the function
             * which performs the Kildalls Analysis
             *************************************************************/
        }
         else {
            System.out.println("Method not found: " + tMethod);
        }
    }
}