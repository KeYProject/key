package visualdebugger;

import java.io.File;
import java.net.URI;
import java.net.URISyntaxException;
import java.util.LinkedList;

import org.eclipse.core.resources.*;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.jdt.core.IClasspathEntry;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.launching.JavaRuntime;

import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.unittest.ModelGenerator;
import de.uka.ilkd.key.unittest.UnitTestBuilder;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class VBTBuilder {
   
    VisualDebugger vd = VisualDebugger.getVisualDebugger();
    ListOfNode nodes;
    private boolean error=false;
    private String file=null;
    IProject testGenProject=null;
    private String fileName;
    private String path;
    private boolean projectCreated=false;
    private int modelGenerator;
    
    
    public VBTBuilder(ListOfNode nodes,int modelGenerator){
        this.nodes=nodes;
        this.modelGenerator=modelGenerator;
        this.createTestCase();
        this.findTestProjectInWorkspace();      
        
        if (testGenProject!=null){
            try {
              testGenProject.refreshLocal(IResource.DEPTH_INFINITE, null);
          } catch (CoreException e) {
              error=true;
              e.printStackTrace();
          }
        } else {
            try {
                projectCreated=true;
              testGenProject = createTestCaseProject(path);
          } catch (URISyntaxException e) {
              error=true;
              e.printStackTrace();
          } catch (CoreException e) {
              error=true;
              e.printStackTrace();
          }
        }
        VisualDebugger.print("------- Test Cases --------");
        VisualDebugger.getVisualDebugger().printTestCases();
        
    }
    
    
    
    
    
    private void findTestProjectInWorkspace(){
        
        final IProject[] projects = ResourcesPlugin.getWorkspace().getRoot().getProjects(); 

        for(int i=0;i<projects.length;i++){
            if (file.startsWith(projects[i].getLocation().toOSString()))
                    testGenProject = projects[i];                  
        }
        
        VisualDebugger.print("Testgenproject "+testGenProject);

        
    }
    


    public void createTestCase(){    
	ModelGenerator.decProdForTestGen=this.modelGenerator;
	UnitTestBuilder testBuilder = new UnitTestBuilder(vd.getMediator().getServices(), 
		vd.getMediator().getProof());

	try{
	    file = testBuilder.createTestForNodes(nodes);
	}catch(Exception e){
	    this.error=true;
	    e.printStackTrace();
	}
	if (file.lastIndexOf(File.separator)>0){
	    int last = file.lastIndexOf(File.separator);
	    fileName =file.substring(last,file.length());
	    path = file.substring(0, last);
	}

    }

     
    private IProject createTestCaseProject(String testFilePath) throws URISyntaxException, CoreException{
        String projectName = "TestCases";
        VisualDebugger.print("Creating new Project in path: "+testFilePath);

        IWorkspace workspace = ResourcesPlugin.getWorkspace();
        IProject project2 = workspace.getRoot().getProject(projectName);
        IProjectDescription projectDescription = null;
        if (!project2.exists())
        {
            URI projectLocationURI=null;
                projectLocationURI = new URI("file:"+testFilePath);
          projectDescription = ResourcesPlugin.getWorkspace().newProjectDescription(projectName);

          if (projectLocationURI != null)
          {
                projectDescription.setLocationURI(new java.net.URI(projectLocationURI.toString()));
          }
            project2.create(projectDescription, null);
        }
        
        if (!project2.isOpen()) {           
                    project2.open(null);
           
        }
        IJavaProject javaProject = JavaCore.create(project2);
        
  
            addNatureToProject(project2, JavaCore.NATURE_ID, null);
  
            javaProject.setRawClasspath(new IClasspathEntry[0], null);
        IPath projectPath = javaProject.getProject().getFullPath();
        VisualDebugger.print("ProjectPath "+projectPath);
        try {
            addContainerEntry(javaProject, new Path(JavaRuntime.JRE_CONTAINER));            
            IClasspathEntry cpe; 
            Path[] dir= getDirectories(new File(VisualDebugger.tempDir));
            
            for (int i=0;i< dir.length;i++){
                String s = dir[i].toOSString();
                //System.out.println("S "+ s.substring(1, s.length()));
            cpe= JavaCore.newSourceEntry(projectPath.append(new Path(s.substring(1, s.length()))));
            addToClasspath(javaProject,cpe);
            }
            
            
//            IPath[] ps = new Path[1];
//            ps[0] = (new Path("home/**"));
            
            IPath[] ps = getExcludingDirectories(new File(testFilePath));
            cpe = JavaCore.newSourceEntry(projectPath.append(new Path("")), ps);
            addToClasspath(javaProject,cpe);
            addContainerEntry(javaProject,new Path("org.eclipse.jdt.junit.JUNIT_CONTAINER/3.8.1"));
        } catch (JavaModelException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
        IProject pro = javaProject.getProject();

        
        return pro;
        
        
//        <?xml version="1.0" encoding="UTF-8"?>
//        <classpath>
//                <classpathentry excluding="home/baum/tmp/visualdebugger/NaturalNumberWrapper/" kind="src" path=""/>
//                <classpathentry kind="src" path="home/baum/tmp/visualdebugger/NaturalNumberWrapper"/>
//                <classpathentry kind="con" path="org.eclipse.jdt.launching.JRE_CONTAINER"/>
//                <classpathentry kind="con" path="org.eclipse.jdt.junit.JUNIT_CONTAINER/3.8.1"/>
//                <classpathentry kind="output" path="bin"/>
//        </classpath>

        
        

    }


    
    private static Path[] getExcludingDirectories(File path){
        LinkedList dir= new LinkedList();
        String[] files = path.list();
        
        for(int i=0;i<files.length;i++){
            //System.out.println("File"+files[i]);
            if (new File(path.toString()+File.separator+files[i]).isDirectory()){
                dir.addLast(new Path(files[i]+File.separator+"**"));
                //System.out.println("dir "+files[i]);
            }
            
        }
        Path[] result = new Path[dir.size()];
        result = (Path[])dir.toArray(new Path[dir.size()]);
        
     return result;   
    }
    
    
    private static Path[] getDirectories(File path){
        LinkedList dir= new LinkedList();
        String[] files = path.list();
        
        for(int i=0;i<files.length;i++){
            if (new File(path.toString()+File.separator+files[i]).isDirectory()){
                dir.addLast(new Path(path.toString()+File.separator+files[i]));
                
            }
            
        }
        Path[] result = new Path[dir.size()];
        result = (Path[])dir.toArray(new Path[dir.size()]);
        
     return result;   
    }
    
 
     private static void addToClasspath(IJavaProject jproject, IClasspathEntry cpe) throws JavaModelException {
                IClasspathEntry[] oldEntries= jproject.getRawClasspath();
                for (int i= 0; i < oldEntries.length; i++) {
                        if (oldEntries[i].equals(cpe)) {
                                return;
                        }
                }
                int nEntries= oldEntries.length;
                IClasspathEntry[] newEntries= new IClasspathEntry[nEntries + 1];
                System.arraycopy(oldEntries, 0, newEntries, 0, nEntries);
                newEntries[nEntries]= cpe;
                jproject.setRawClasspath(newEntries, null);
        }
    
    public static void addContainerEntry(IJavaProject project, IPath container) throws JavaModelException {
        IClasspathEntry cpe = JavaCore.newContainerEntry(container, false);
        addToClasspath(project, cpe);
}
    
    
    private static void addNatureToProject(IProject proj, String natureId, IProgressMonitor monitor) throws CoreException {
        IProjectDescription description = proj.getDescription();
        String[] prevNatures= description.getNatureIds();
        String[] newNatures= new String[prevNatures.length + 1];
        System.arraycopy(prevNatures, 0, newNatures, 0, prevNatures.length);
        newNatures[prevNatures.length]= natureId;
        description.setNatureIds(newNatures);
        proj.setDescription(description, monitor);
}
    
    
    public boolean succesful(){
        return !this.error;
    }
    
    public boolean newProjectCreated(){
        return projectCreated;
    }





    public IProject getTestGenProject() {
        return testGenProject;
    }





    public String getFileName() {
        return fileName;
    }
    
  

}
