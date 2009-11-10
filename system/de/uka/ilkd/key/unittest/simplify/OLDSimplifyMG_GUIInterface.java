package de.uka.ilkd.key.unittest.simplify;

import java.util.HashMap;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.TestGenerationInspectionDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.unittest.EquivalenceClass;
import de.uka.ilkd.key.unittest.simplify.translation.DecisionProcedureSimplify;

public class OLDSimplifyMG_GUIInterface extends OldSimplifyModelGenerator {

    public OLDSimplifyMG_GUIInterface(DecisionProcedureSimplify dps,
            Services serv, HashMap<Term, EquivalenceClass> term2class,
            ImmutableSet<Term> locations) {
	super(dps, serv, term2class, locations);
	// TODO Auto-generated constructor stub
    }
    
    /**is called from createModels */
    protected void createModels_ProgressNotification1(String initCounterExample, int datCount){
	try{
        	if(Main.isVisibleMode() || Main.standalone){
        	    TestGenerationInspectionDialog dialog = TestGenerationInspectionDialog.getInstance(Main.getInstance());
        	    dialog.msg("--------- Initial Counter Example -------\nDATCOUNT:"+datCount+"\n"+initCounterExample);
        	}
	}catch (Exception e){
	    
	}
    }
    
    /** is called by createModelsHelp*/
    protected void createModelsHelp_ProgressNotification1(String counterExOld){   
//	try{
//    	if(Main.isVisibleMode() || Main.standalone){
//    	    TestGenerationInspectionDialog dialog = TestGenerationInspectionDialog.getInstance(Main.getInstance());
//    	    dialog.msg("------ Initial or old counter example received from Simplify \n"+counterExOld);
//    	}
//	}catch (Exception e){
//	    
//	}	
    }


    /**returns comma separated list of integers that are considered for test data generation */
    public static String getTestData(){
	String res="";
	for(int val:genericTestValues){
	    res+=val+",";
	}
	if(res.endsWith(",")){
	    res=res.substring(0, res.length()-1);
	}
	return res;
    }
    
    /**parse the provided string of comma separated numbers and use the integers for model generation */
    public static void setTestData(String tdStr){
	if(tdStr==null || tdStr.length()==0){
	    System.out.println("Warning: Test data is deleted; this may be undesired.");
	    genericTestValues = new int[0];
	    return;
	}
	String[] numbers= tdStr.split(",");
	if(numbers.length==0){
	    System.out.println("Warning: Invalid test data provided (1)");
	    return;
	}
	int[] newData = new int[numbers.length];
	try{
        	for(int i=0;i<numbers.length;i++){
        	    newData[i] = Integer.parseInt(numbers[i]);
        	}
	}catch(Exception ex){
	    System.out.println("Warning: Invalid test data provided (2)");
	    return;
	}
	genericTestValues = newData;
    }


}
