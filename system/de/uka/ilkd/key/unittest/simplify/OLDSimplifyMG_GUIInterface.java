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
	
    private HashMap<String,CreateModelsInfo> createModelsHelpStat=new HashMap<String,CreateModelsInfo>();
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
	for(String pos:POS){
	    createModelsHelpStat.put(pos, new CreateModelsInfo());
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
    
    private class CreateModelsInfo {
	public int count;
	public int iterativeDeepeningDepth;
	public int recDepth;
	public String info;
	public CreateModelsInfo() {
	    count= 0;
	    info = null;
	}
    }

    /** is called by createModelsHelp*/
    protected void createModelsHelp_ProgressNotificationX(String codePos, int iterativeDeepeningDepth, int recDepth, String info){   
	try{
	    if(Main.isVisibleMode() || Main.standalone){
		CreateModelsInfo cmInfo = createModelsHelpStat.get(codePos);
		cmInfo.count++;
		cmInfo.iterativeDeepeningDepth = iterativeDeepeningDepth;
		cmInfo.recDepth = recDepth;
		cmInfo.info = info;
        	String s ="";
        	for(String pos:POS){
        	    cmInfo = createModelsHelpStat.get(pos);
        	    s += pos + " " + cmInfo.count + spaceForNum(cmInfo.count)
        	    		+ cmInfo.iterativeDeepeningDepth + spaceForNum(cmInfo.iterativeDeepeningDepth)
        	    		+ cmInfo.recDepth + spaceForNum(cmInfo.recDepth)
        	    		+ (cmInfo.info!=null?cmInfo.info:"") +"\n";
        	}
	
		TestGenerationInspectionDialog dialog = TestGenerationInspectionDialog.getInstance(Main.getInstance());
    	    	dialog.createModelsHelpMsg(s);
	    }
	}catch (Exception e){
	    System.out.print("progress notification problem ");
	}
	
    }
    
    private String spaceForNum(int i){
	if(i<=9){
	    return "    ";
	}else if(i<=99){
	    return "   ";
	}else if(i<=999){
	    return "  ";
	}else 
	    return " ";
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
