package de.uka.ilkd.key.testgen;

public interface TestGenSettings {	
	
	
	public int getMaximalUnwinds();
	
	
	public boolean removeDuplicates();
	
	
	public boolean useJunit();
	
	
	public int getNumberOfProcesses();
	
	
	public String getOutputFolderPath();
	
	public boolean invaraiantForAll();
	
	
}
