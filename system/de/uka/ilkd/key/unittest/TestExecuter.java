package de.uka.ilkd.key.unittest;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.util.Vector;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.Main;

/**
 * A Utility class for compiling and running test source files
 * @author gladisch
 */
public class TestExecuter {
    	//static String junitpath = System.getProperty("key.home") + File.separator + "junit.jar";
	private static String classpath = null;

	public static String[] testCompilationCommand(String testPath, boolean compileOnlyGeneratedFiles){
	    	assert(testPath.indexOf('\n')==-1);
		String test = testPath.substring(testPath.lastIndexOf(File.separator) + 1);
		String testDir = testPath.substring(0, testPath.lastIndexOf(File.separator));

		Vector<String> cmdAndArgs = new Vector<String>();
		cmdAndArgs.add("javac");
		cmdAndArgs.add("-cp");
		cmdAndArgs.add(getClasspath());
		Vector<String> files = new Vector<String>();
		if (compileOnlyGeneratedFiles) {
			files.add(test);
			File fileRFL = new File(testDir + File.separator + "RFL.java");
			System.out.println("RFL file:" + fileRFL + "   exists:"	+ fileRFL.exists());
			if (fileRFL.exists())
				files.add(fileRFL.toString());
		} else {
			System.out.println("testDir:" + testDir);
			files = getJavaFilesAsStrings(testDir, true);
		}
		assert(files.size()>0);
		cmdAndArgs.addAll(files);
		String[] stArray = cmdAndArgs.toArray(new String[0]);
		return stArray;
	    }
	    
	public static String[] testExecutionCommand(String testPath, boolean GUImode){
	    	assert(testPath.indexOf('\n')==-1);
		String test = testPath.substring(testPath.lastIndexOf(File.separator) + 1);
		String testDir = testPath.substring(0, testPath.lastIndexOf(File.separator));

		Vector<String> cmdAndArgs = new Vector<String>();
	        cmdAndArgs.add("java");
	        cmdAndArgs.add("-cp");
	        cmdAndArgs.add(getClasspath());

	        if(GUImode){
	        	cmdAndArgs.add("junit.swingui.TestRunner");
	        }else{
	        	cmdAndArgs.add("junit.textui.TestRunner");
	        }
	        cmdAndArgs.add(test.substring(0, test.lastIndexOf(".")));
	   		String[] stArray = cmdAndArgs.toArray(new String[0]);

	        return stArray;
	    }
	    
	    /**
	     * @param testPath the full path to the test suite file
	     * @param modelDir is currently not supported
	     * @throws IOException
	     */
	public static void compileAndRunTest(String testPath, String workingDir, boolean compileOnlyGeneratedFiles,boolean GUImode) throws IOException{
	    	assert(testPath.indexOf('\n')==-1);
		File workingDirFile = null;
		if(workingDir!=null && !workingDir.equals("")){
			workingDirFile = new File(workingDir);
		}else{
			workingDirFile = new File(testPath.substring(0, testPath.lastIndexOf(File.separator)));
		}
		//System.out.println("testPath:"+testPath+"\nWorking dir:"+workingDirFile.getAbsolutePath()+ "    exists:"+workingDirFile.exists());
	        Runtime rt = Runtime.getRuntime();
	        String[] execStr = testCompilationCommand(testPath,compileOnlyGeneratedFiles);
	        
	        Process compile = rt.exec(execStr, null, workingDirFile);
	        String compileError = read(compile.getErrorStream()).trim();
	        if(!"".equals(compileError)){
	            throw new RuntimeException(compileError);
	        }
	        
	        execStr = testExecutionCommand(testPath,GUImode);
	        Process runJUnit = rt.exec(execStr, null, workingDirFile);
	        String junitError = read(runJUnit.getErrorStream());
	        if(!"".equals(junitError)){
	            throw new RuntimeException(junitError);
	        }   
	    }
	    
	    public static Vector<String> getJavaFilesAsStrings(String basePath, boolean recursively){
	    	Vector<File> files = getJavaFiles(new File(basePath),recursively);
	    	Vector<String> res = new Vector<String>();
	    	for(File f:files)
	    		res.add(f.getAbsolutePath());
	    	return res;
	    }
	    
	    public static Vector<File> getJavaFiles(File basePath, boolean recursively){
	    	assert(basePath.exists());
	    	File[] files = basePath.listFiles(new java.io.FileFilter(){
	    		public boolean accept(File pathname){
	    			return pathname.isFile() && pathname.getAbsolutePath().endsWith(".java");
	    		}
	    	});
	    	Vector<File> fileVect = new Vector<File>();
	    	if(files!=null)
        	    	for(File f:files)
        	    		fileVect.add(f);
	    	
	    	if(recursively){
	        	File[] dirs = basePath.listFiles(new java.io.FileFilter(){
	        		public boolean accept(File pathname){
	        			return pathname.isDirectory();
	        		}
	        	});
		    	if(dirs!=null){
        	        	for(File dir:dirs){
        		    		Vector<File> subFiles = getJavaFiles(dir,recursively);
        		    		for(File f:subFiles){
        		    			fileVect.add(f);
        		    		}
        		    	}
		    	}
	    	}
	    	return fileVect;
	    }

	    protected static  String read ( InputStream in ) throws IOException {
	        String lineSeparator = System.getProperty("line.separator");
	        BufferedReader reader = new BufferedReader
	            (new InputStreamReader(in));
	        StringBuffer sb = new StringBuffer();
	        String line;
	        while ((line = reader.readLine()) != null) {
	            sb.append(line).append(lineSeparator);
	        }
	        return sb.toString();
	    }

	    public static void setClasspath(String classpath) {
	        TestExecuter.classpath = classpath;
            }

	    public static String getClasspath() {
		if(classpath==null){
		    String keyhome = System.getProperty("key.home");
		    if(keyhome==null){
			if(Main.isVisibleMode() || Main.testStandalone){
			    JOptionPane.showMessageDialog(Main.getInstance(),
				    "The environment variable \"key.home\" is not set",
				    "Warning",
				    JOptionPane.WARNING_MESSAGE);
			}else{
			    System.out.println("The environment variable \"key.home\" is not set");
			}
		    }else{
			classpath=keyhome+File.separator+"key-ext-jars"+File.separator+"junit.jar"+
				":"+keyhome+File.separator+"key-ext-jars"+File.separator+"objenesis.jar";
			if(File.separatorChar=='/')
			    classpath+=":./";
		    }
		}
	        return classpath;
            }

}
