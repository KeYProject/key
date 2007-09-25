// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.casetool.together.scripts.patternmechanism;

import java.io.*;
import java.util.LinkedList;

import com.togethersoft.openapi.ide.IdeContext;
import com.togethersoft.openapi.ide.command.*;
import com.togethersoft.openapi.ide.diagram.IdeDiagramManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageType;
import com.togethersoft.openapi.rwi.*;
import com.togethersoft.openapi.vfs.VirtualFile;
import com.togethersoft.openapi.vfs.VirtualFileManagerAccess;

import de.uka.ilkd.key.casetool.patternimplementor.PatternMechanism;
import de.uka.ilkd.key.casetool.patternimplementor.PatternMechanismUI;
import de.uka.ilkd.key.casetool.patternimplementor.SourceCode;
import de.uka.ilkd.key.casetool.together.TogetherOCLSimplInterface;
import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyScript;

public class KeYPatternMechanism extends KeyScript {

    private IdeCommandGroup myGroup; // command group
    private IdeCommandItem myItem2; // command item

    /**
     * Runs this module.
     * 
     * @param context
     *            the IdeContext instance containing the selection information
     *            at the moment the module was called.
     */
    public void run1(IdeContext context) {
        // printing message into message pane
        IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,
                "KeY module : started");

        // menu creation
        createTheMenu();

        // printing final message
        IdeMessageManagerAccess.printMessage(IdeMessageType.INFORMATION,
                "KeY module: finished");
    }

    /**
     * This method is called while Together is loading.
     */
    public void autorun1() {
        // creation menu in processs of Together loading (startup).
        createTheMenu();
    }

    /**
     * Creates popup menu (adding menus and command in popup menu)
     */
    private void createTheMenu() {
        // getting IdeCommandManager object
        IdeCommandManager cman = IdeCommandManagerAccess.getCommandManager();

        // create a new command group which can be used as a container
        // for other command items
        this.myGroup = cman.createGroup("IDOfTheGroup", // identifier

                // constraint object witch defines constraints for the command
                // items
                new IdeCommandConstraints("context = element, " + "shapeType="
                        + RwiShapeType.CLASS_DIAGRAM + ", " +
                        //"shapetype=" + RwiShapeType.CLASS + ", " +
                        "location=popupMenu"),

                /*
                 * ... shapeType=Class,
                 * shapeType="+RwiShapeType.CLASS_DIAGRAM+", location...
                 */

                // Now, the constraints mechanism works so, that it will run
                // checkStatus method (below) only, if the shapetype of the
                // element
                // equals the specified value "Class" ( for classes and
                // interfaces ).
                // listener object for receiving command events from items and
                // groups
                new IdeCommandCheckListener() {

                    public void checkStatus(IdeCommandEvent event) {
                        // getting the element(s) under cursor
                        // getting context
                        IdeContext context = event.getElementContext();

                        // getting array of selected elements from context
                        RwiElement[] selectedRwiElements = context
                                .getRwiElements();

                        // getting selected element
                        RwiElement theElement = selectedRwiElements[0];

                        // set group text
                        event.getCommandItem().setText("KeY Design Pattern");
                    }
                });

        // create second item
        // Note: the "placeAfter" parameter, there we specify the ID of the
        // myItem
        myItem2 = cman.createItem("IDOfTheItem2", new IdeCommandConstraints(
                "context = element, parent=IDOfTheGroup" /*
                                                          * , placeAfter =
                                                          * IDOfTheItem
                                                          */
                        + ", location=popupMenu"), new IdeCommandAdapter() {

				// The item is always visible, so
				// we use the empty checkStatus method.
				// the user managed to invoke the command
				public void actionPerformed(IdeCommandEvent event) {
				    // making message pane visible
				    IdeMessageManagerAccess.getMessageManager()
					.setPaneVisible(true);

				    // printing message
				    IdeMessageManagerAccess.printMessage(
									 IdeMessageType.INFORMATION,
									 "Debug : Insert Design Pattern");

				    PatternMechanism pm = new PatternMechanism();
				    new PatternMechanismUI(pm);

				    //doSomeWork("Hello");
				    //doSomeWork("Tjohoo");
				    if (pm.getImplementation() != null) {
					saveSourceCode(pm.getImplementation());
				    }
				}
			    });
        myItem2.setText("Insert Design Pattern"); // set item text

        // making message pane visible
        IdeMessageManagerAccess.getMessageManager().setPaneVisible(true);

        // printing message
        IdeMessageManagerAccess
	    .printMessage(
			  IdeMessageType.INFORMATION,
			  "KeY module: new popup submenu for classes/interfaces was successfully created.");
    }

    public void saveSourceCode(SourceCode sc) {
        final int numberOfClasses = sc.nofClasses();
	//Added by Daniel
	LinkedList newClasses = new LinkedList();
	//
        for (int i = 0; i < numberOfClasses; i++) {
            SourceCode tmp = sc.getClass(i);

            String codeStr = tmp.toText();
            
	    //SourceCode$ClassDelimiter::name
            String filename = tmp.getClassName();

	    //Added by Daniel
	    //filename has the form: "<class_name>.java"
	    newClasses.add(filename.substring(0, filename.indexOf(".")));
	    //

            /*RwiDiagram activeDiagram;
            RwiPackage subpackage;
            RwiNode node;
            String path;*/
            String absolutefilename = getCurrentPath(filename);

            saveToFile(codeStr, absolutefilename);
        }

	//Added by Daniel
	//(new TogetherOCLSimplInterface()).simplifyConstraints(newClasses);
	//
    }
    /**
     * 
     * getCurrentPath("hello") returns "/path/to/hello.java"
     * getCurrentPath("world.java") returns "/path/to/world.java" 
     * 
     * @param filename
     * @return returns a complete path to a file that should be (or are) in the active diagram.
     */
    private String getCurrentPath(String filename) {
        RwiDiagram activeDiagram = IdeDiagramManagerAccess
                .getDiagramManager().getActiveDiagram().getRwiDiagram();

        RwiPackage subpackage = activeDiagram.getContainingPackage();

        RwiNode node;

        /*
         * if(subpackage.canCreateNodeByPattern(RwiLanguage.JAVA,
         * RwiPattern.DEFAULT_CLASS)) { }
         */

        
        //   http://i12www.ira.uka.de/~klebanov/doc/together-api/com/togethersoft/openapi/rwi/RwiPackage.html#createNodeByPattern(java.lang.String,%20java.lang.String)
        node = subpackage.createNodeByPattern(RwiLanguage.JAVA,
                RwiPattern.DEFAULT_CLASS);
        node.setProperty(RwiProperty.NAME, filename);
        String absolutefilename = node.getProperty(RwiProperty.FILE);
        // node.delete() is safe because:
        // if the file exists then (the created node has another name)
        // else (the file didn't exist before, then it's ok to delete since it is empty)
        node.delete();
        //----------------------------
        String path = absolutefilename.substring(0, absolutefilename
                .lastIndexOf(File.separatorChar) + 1);
        //String realFilename =
        // absolutefilename.substring(absolutefilename.lastIndexOf(File.separatorChar)+1,absolutefilename.lastIndexOf('.'));
        if (filename.indexOf(".java") != -1) {
            filename = filename.substring(0, filename.indexOf(".java"));
        }
        absolutefilename = path + filename + ".java";
        return absolutefilename;
    }

    private void saveToFile(String codeStr, String absolutefilename) {
        try {
            File outFile = new File(absolutefilename);
            /**
             * If file already exists, place the contents of the existing file
             * in the end of the new file with '//' before each line.
             */
            if (outFile.exists()) {

                //System.err.println("File exists!!! - se till att all kod
                // finns kvar");
                /*
                 * throw new Exception("File " + absolutefilename + " exists!");
                 */
                BufferedReader in = new BufferedReader(new FileReader(outFile));
                String oldContents = new String();
                while (in.ready()) {
                    String tmp = "// " + in.readLine() + "\n";
                    oldContents = oldContents + tmp;
                }
                in.close();
                codeStr = codeStr + "\n" + oldContents;
            }
            PrintWriter out = new PrintWriter(new BufferedWriter(
                    new FileWriter(outFile)));

            out.println(codeStr);
            out.flush();
            out.close();
        } catch (Exception e) {
            e.printStackTrace();
        }


        VirtualFile vf = VirtualFileManagerAccess.getVirtualFileManager()
                .getVirtualFile(absolutefilename);
        try {
            VirtualFileManagerAccess.getVirtualFileManager().externalUpdate(vf,
                    true);
        } catch (IOException e1) {
            // TODO Auto-generated catch block
            e1.printStackTrace();
        }
    }
}
