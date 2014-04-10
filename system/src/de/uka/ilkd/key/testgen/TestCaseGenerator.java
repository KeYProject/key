package de.uka.ilkd.key.testgen;

import java.util.LinkedList;
import java.util.List;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.smt.model.Heap;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.model.ObjectVal;

public class TestCaseGenerator {
	
	Services services;
	
	String PREFIX = "import junit.framework.*;"
			+ "\n public class TestGeneric0 extends junit.framework.TestCase {"
			+ "\n  public TestGeneric0(){}"
			+ "\n  public static junit.framework.TestSuite suite () {"
			+ "\n junit.framework.TestSuite suiteVar;"
			+ "\n suiteVar=new junit.framework.TestSuite (TestGeneric0.class);"
			+ "\n return  suiteVar;}";
	String MAIN = " public static void  main (java.lang.String[]  arg) {"
			+ "\n     TestGeneric0 testSuiteObject;"
			+ "\n     testSuiteObject=new TestGeneric0 ();"
			+ "\n     testSuiteObject.testcode0();}";
	
	String TESTCODE = "public void  testcode0 () {";
	String POSTFIX = "}";
	String MUT = "self.maxarrayErr(a)";
	
	
	
	public TestCaseGenerator(Services services) {
		super();
		this.services = services;
	}

	private boolean filterVal(String s){
		if(s.startsWith("#a")||s.startsWith("#s")||s.startsWith("#h")||s.startsWith("#l")||s.startsWith("#f")){
			return false;
		}
		else{
			return true;
		}
	}
	
	private ObjectVal getObject(Heap h,String name){
		if(h==null){
			return null;
		}
		for(ObjectVal o : h.getObjects()){
			if(o.getName().equals(name)){
				return o;
			}
		}
		return null;
	}
	
	public String generateJUnitTestCase(Model m){
		return PREFIX + "\n"+MAIN+"\n"+TESTCODE+"\n"+generateTestCase(m)+"\n"+MUT+"\n"+POSTFIX+"}";
	}

	public String generateTestCase(Model m){
		
		List<Assignment> assignments = new LinkedList<Assignment>();
		
		Heap heap = null;
		for(Heap h : m.getHeaps()){
			if(h.getName().equals("heap")){
				heap = h;
				break;
			}
		}
		
				
		
		if(heap!=null){
			//create objects
			for(ObjectVal o : heap.getObjects()){
				if(o.getName().equals("#o0")){
					continue;
				}
				
				String type = o.getSort().name().toString();
				String right;				
				if(type.endsWith("[]")){
					right = "new "+type.substring(0, type.length()-2)+"["+o.getLength()+"]";
				}
				else{
					right = "new "+type+"()";
				}
				assignments.add(new Assignment(type, o.getName().replace("#", ""), right));
				
				
			}			
		}
		//init constants
		for(String c : m.getConstants().keySet()){
			String val = m.getConstants().get(c);
			if(filterVal(val) && !c.equals("null")){
				String type = "int";
				if(val.equals("true")||val.equals("false")){
					type = "boolean";
				}
				else if(val.startsWith("#o")){
					ObjectVal o = getObject(heap, val);
					if(o!=null){
						type = o.getSort().name().toString();
					}
					else{
						type = "Object";
					}
				}				
				val = val.replace("#", "");
				assignments.add(new Assignment(type,c,val));
			}
		}
		
		//init fields
		if(heap!=null){
			
			for(ObjectVal o : heap.getObjects()){
				if(o.getName().equals("#o0")){
					continue;
				}
				
				String name = o.getName().replace("#", "");
				
				for(String f : o.getFieldvalues().keySet()){
					if(f.contains("<") || f.contains(">")){
						continue;
					}
					String fieldName = f.substring(f.lastIndexOf(":")+1);
					fieldName = fieldName.replace("|", "");
					String val = o.getFieldvalues().get(f);
					if(val.contains("/")){
						val = val.substring(0, val.indexOf("/"));
					}
					val = val.replace("|", "");
					assignments.add(new Assignment(name+"."+fieldName, val));
				}
				
				for(int i = 0; i < o.getLength(); i++){
					String fieldName = "["+i+"]";
					String val = o.getArrayValue(i);
					if(val.contains("/")){
						val = val.substring(0, val.indexOf("/"));
					}
					assignments.add(new Assignment(name+fieldName, val));
				}				
			}			
		}
		
		
		String result = "";
		for(Assignment a : assignments){
			result+=a.toString();
		}
		
		
		
		return result;
	}

}
