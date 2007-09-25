// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/**
 * Creates the KeY-menus to be used in the Together-Tool.
 * Assumes, that classes of form GlobalMenu<No>, ClassMenu<No>, OpMenu<No>
 * reside in the same package.
 */



package de.uka.ilkd.key.casetool.together.scripts.menuextension;

import java.util.ResourceBundle;

import javax.swing.ImageIcon;
import javax.swing.JOptionPane;

import com.togethersoft.openapi.ide.IdeContext;
import com.togethersoft.openapi.ide.command.*;
import com.togethersoft.openapi.ide.message.IdeMessageManagerAccess;
import com.togethersoft.openapi.ide.message.IdeMessageType;
import com.togethersoft.openapi.ide.window.IdeWindowManager;
import com.togethersoft.openapi.ide.window.IdeWindowManagerAccess;

import de.uka.ilkd.key.casetool.together.keydebugclassloader.KeyScript;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYResourceManager;


public class KeyMenuExtension extends KeyScript  {

    /**
     * Program resources.
     */
    protected static final ResourceBundle resources;
    static {
	try {
	    resources = ResourceBundle.getBundle(KeyMenuExtension.class.getName());
	} catch (ExceptionInInitializerError e) {
	    JOptionPane.showMessageDialog(null, "An error occured initializing " + 
					  KeyMenuExtension.class.getName() + 
					  ".\nThe package seems corrupt or a resource is missing, aborting\n" 
					  + e, "Error", JOptionPane.ERROR_MESSAGE);
	    throw new InternalError(e.getMessage())/*.initCause(e)*/;
	} catch (LinkageError le) {
	    JOptionPane.showMessageDialog(null, "An error occured in linking class " + 
					  KeyMenuExtension.class.getName() + 
					  ".\nThe package seems corrupt or a resource is missing, aborting\n" 
					  + le, "Error", JOptionPane.ERROR_MESSAGE);
	    throw new InternalError(le.getMessage())/*.initCause(e)*/;
	}
    }

    
    // auxiliary variables
    IdeCommandManager comMan = IdeCommandManagerAccess.getCommandManager();
    IdeWindowManager winMan = IdeWindowManagerAccess.getWindowManager();
    String myPackageName = this.getClass().getPackage().getName();


    /** Reactivate the script */
    public void run1(IdeContext context) {
	autorun1();
    }
 
    /**
     * Activate the script (cmp. KeyScript)
     */ 
    public void autorun1() {
        de.uka.ilkd.key.gui.Main.configureLogger();
        IdeMessageManagerAccess.printMessage
	    (IdeMessageType.INFORMATION, "KeyMenuExtension new script: started");
        createAllMenus();
	de.uka.ilkd.key.proof.init.OCLProofOblInput.setModelManager
	    (de.uka.ilkd.key.casetool.together.TogetherModelManager.INSTANCE);
        IdeMessageManagerAccess.printMessage
	    (IdeMessageType.INFORMATION, "KeyMenuExtension script: finished");
    }


    private void createAllMenus() {
	//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
	//xxx to re-activate the KeY menu group uncomment the following line
	//XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX
	//       	createGlobalMenus();
	// instead of the XMI transform menu point we create  "about" and "license" menue points
	createGlobalMenus2();
	createClassContextMenus();
	createOperationContextMenus();
    }



    //control variables for global menus
    static int NUMGLOBALMENUTYPES = 2;
    static int NUMGLOBALMENUGROUPS = 1;
    public IdeCommandGroup[][] myGlobalMenuGroups = new IdeCommandGroup[NUMGLOBALMENUTYPES][NUMGLOBALMENUGROUPS];
    IdeCommandGroup myMainMenuGroup;
    IdeCommandGroup myMainToolbarGroup;




    private void createGlobalMenus(){
 	String[] globalMenuLocation = new String[] { "mainToolbar", "mainMenu"};

	//creates the group-item in the global menu
	myMainMenuGroup = comMan.createGroup("IDOf"+globalMenuLocation[1], 
					     new IdeCommandConstraints("location="+globalMenuLocation[1]),
					     new IdeCommandCheckListener() {
						     public void checkStatus(IdeCommandEvent event) {
							 myMainMenuGroup.setText("KeY");               
						     }
						 }
 					     );


	// The main toolbar is extended with our own icon (KeY-button)
	//	String tjextpath = System.getProperty("KeyPathTjext");
	//	final ImageIcon icon = new ImageIcon(tjextpath + "/de/uka/ilkd/key/casetool/together/scripts/menuextension/key-color-icon-small.gif");

	final ImageIcon icon = KeYResourceManager.getManager().createImageIcon(this, "key-color-icon-small.gif");
	myMainToolbarGroup = comMan.createGroup("IDOf"+globalMenuLocation[0], 
						new IdeCommandConstraints("location="+globalMenuLocation[0]),
						new IdeCommandCheckListener(){ 
							// we have to mention checkStatus because of IdeCommandCheckListener is
							// an interface, not a class where you can create instances of
							public void checkStatus(IdeCommandEvent event) {
							}
						    }
						);
	
	//The icon is set to the new ToolbarGroup
	myMainToolbarGroup.setIcon(IdeCommandIconType.PRESSED, icon);
	myMainToolbarGroup.setIcon(IdeCommandIconType.DEFAULT, icon);


	// All used Items in the global menu have a name of form "GlobalMenu.."
	// That classes are in the same package as that class.
	String globalMenuRootCN = myPackageName + "." + "GlobalMenu";
	for (int typeI = 0; typeI < NUMGLOBALMENUTYPES; typeI++){
	    for (int group = 1; group < (NUMGLOBALMENUGROUPS +1) ; group++){
		myGlobalMenuGroups[typeI][(group-1)] = comMan.createGroup("IDOfTheMainMenuSubGroup"+globalMenuLocation[typeI] + group, 
									  new IdeCommandConstraints("parent=IDOf"+globalMenuLocation[typeI]+", location="+globalMenuLocation[typeI]),
									  // 				new IdeCommandCheckListener() {
									  // 					public void checkStatus(IdeCommandEvent event) {
									  // 					    // here we create an instance of classes like GlobalMenueGroup1
									  // 					    ( myGlobalMenuGroups[typeI][(group-1)]).setText(((GlobalMenue) Class.forName(globalMenueRootCN + "Group" + group).newInstance()).getMenueEntry());               
									  // 					}
									  // 				    }
									  //				 new KeyMenuIdeCmdListener(this, typeI, (group-1), globalMenuRootCN) 	   
									  new GlobalMenuIdeAdapter(this, null, typeI, group, 0, globalMenuRootCN) 	   
									      );

		// how many entries have the groups
		int groupElemNum;
		if (group == 1){groupElemNum = 1;}
		else if (group == 2){groupElemNum = 0;}
		else if (group == 3){groupElemNum = 0;}
		else {groupElemNum = 0;}


		for (int groupItem = 1; groupItem < (groupElemNum + 1); groupItem++){
		    // generating the elements of the groups

		    // at first we generate an adapter to cover the functionality

		    // 		    IdeCommandAdapter actAdapter = new IdeCommandAdapter() {
		    // 			    public void actionPerformed(IdeCommandEvent event) { 
		    // 				// here we create an instance of classes like GlobalMenuePoint1_1
		    // 				try{
		    // 				    ((GlobalMenue) Class.forName(globalMenueRootCN + "Point" + group + "_" + groupItem).newInstance()).run(winMan);
		    // 				}catch(Exception e){
		    // 				    System.err.println("KeYError: " + e);
		    //                                  e.printStackTrace();
		    // 				}
		    // 			    }
		    // 			};

		    GlobalMenuIdeAdapter actAdapter = new GlobalMenuIdeAdapter(this, winMan, 0, group, groupItem, globalMenuRootCN);
			

		    // now the menuentry of the actual group
		    String optionalPlaceAfterString = "";
		    if (groupItem > 1){optionalPlaceAfterString = ", placeAfter = IDOfItem"+globalMenuLocation[typeI]+group+"_"+(groupItem-1);}

		    IdeCommandItem groupElement = comMan.createItem
			("IDOfItem"+globalMenuLocation[typeI]+group+"_"+groupItem,
			 new IdeCommandConstraints("parent=IDOfTheMainMenuSubGroup"+
						   globalMenuLocation[typeI] + 
						   group + optionalPlaceAfterString + 
						   ", location="+globalMenuLocation[typeI]),
			 actAdapter);

		    // here we create an instance of classes like GlobalMenuPoint1_1
		    try{
			groupElement.setText
			    (((GlobalMenu) Class.forName
			      (globalMenuRootCN + "Point" + 
			       group + "_" + groupItem).newInstance()).getMenuEntry());
			
		    }  catch (ClassNotFoundException cnfe) {
			System.err.println("keymenuextension: class cannot be located");
			System.err.println("The exception was: "+cnfe);
			cnfe.printStackTrace();
		    } catch (ExceptionInInitializerError ei) {
			System.err.println("keymenuextension: the initialization provoked "+
					   "by this method fails.");
			System.err.println("The exception was: "+ei);
			ei.printStackTrace();
		    } catch (IllegalAccessException iae) {
			System.err.println("keymenuextension: class or "+
					   "initializer is not accessible."); 
			System.err.println("The exception was: "+iae); 
			iae.printStackTrace(); 
		    } catch (InstantiationException ie) { 
			System.err.println
			    ("keymenuextension: class tried to\n"+
			     "instantiate represents an abstract class, an interface,"+
			     "an array class, a primitive type, or void; or if the"+
			     "instantiation fails for some other reason.");  
			System.err.println("The exception was: "+ie);  
			ie.printStackTrace();
		    } catch (SecurityException se) {
			System.err.println("keymenuextension: no permission to create"+
					   "a new instance"); 
			System.err.println("The exception was: "+se); 
			se.printStackTrace(); 
		    } catch (LinkageError le) {
			System.err.println("keymenuextension: linkage failed");
			System.err.println("The exception was: "+le);
			le.printStackTrace();
		    }

		    groupElement.setEnabled(true);
		    groupElement.setVisible(true);
		    groupElement.setSeparatorAfter(true);
		}
	    }
	}
    }


    private void createGlobalMenus2(){
 	String[] globalMenuLocation = new String[] { "mainToolbar", "mainMenu"};

	//creates the group-item in the global menu
	myMainMenuGroup = comMan.createGroup("IDOf"+globalMenuLocation[1], 
					     new IdeCommandConstraints("location="+globalMenuLocation[1]),
					     new IdeCommandCheckListener() {
						     public void checkStatus(IdeCommandEvent event) {
							 myMainMenuGroup.setText("KeY");               
						     }
						 }
 					     );

	final ImageIcon icon = KeYResourceManager.getManager().createImageIcon(this, "key-color-icon-small.gif");
	myMainToolbarGroup = comMan.createGroup("IDOf"+globalMenuLocation[0], 
						new IdeCommandConstraints("location="+globalMenuLocation[0]),
						new IdeCommandCheckListener(){ 
							public void checkStatus(IdeCommandEvent event) {
							}
						    }
						);
	
	//The icon is set to the new ToolbarGroup
	myMainToolbarGroup.setIcon(IdeCommandIconType.PRESSED, icon);
	myMainToolbarGroup.setIcon(IdeCommandIconType.DEFAULT, icon);


	// All used Items in the global menu have a name of form "GlobalMenu.."
	// That classes are in the same package as that class.
	String globalMenuRootCN = myPackageName + "." + "GlobalMenu";
	for (int typeI = 0; typeI < NUMGLOBALMENUTYPES; typeI++){
	    int group=1;
	                  
	    // now the menuentry of the actual group	
	    
	    IdeCommandItem groupElement1 = comMan.createItem
		("IDOfMenuPoint1"+globalMenuLocation[typeI] + group, 
		 new IdeCommandConstraints
		     ("parent=IDOf"+globalMenuLocation[typeI]+
		      ", location="+globalMenuLocation[typeI]),
		 new GlobalMenuIdeAdapter
		     (this, winMan, typeI, group, 2 , globalMenuRootCN));
	    IdeCommandItem groupElement2 = comMan.createItem
		("IDOfMeuPoint2"+globalMenuLocation[typeI] + group, 
		 new IdeCommandConstraints
		     ("parent=IDOf"+globalMenuLocation[typeI]+
		      ", location="+globalMenuLocation[typeI]),
		 new GlobalMenuIdeAdapter
		     (this, winMan, typeI, group, 3 , globalMenuRootCN));	    
	    IdeCommandItem groupElement4 = comMan.createItem
		("IDOfMeuPoint4"+globalMenuLocation[typeI] + group, 
		 new IdeCommandConstraints
		     ("parent=IDOf"+globalMenuLocation[typeI]+
		      ", location="+globalMenuLocation[typeI]),
		 new GlobalMenuIdeAdapter
		     (this, winMan, typeI, group, 4 , globalMenuRootCN));	    
	    IdeCommandItem groupElement5 = comMan.createItem
		("IDOfMeuPoint5"+globalMenuLocation[typeI] + group, 
		 new IdeCommandConstraints
		     ("parent=IDOf"+globalMenuLocation[typeI]+
		      ", location="+globalMenuLocation[typeI]),
		 new GlobalMenuIdeAdapter
		     (this, winMan, typeI, group, 5 , globalMenuRootCN));
	    IdeCommandItem groupElement6 = comMan.createItem
		("IDOfMeuPoint6"+globalMenuLocation[typeI] + group, 
		 new IdeCommandConstraints
		     ("parent=IDOf"+globalMenuLocation[typeI]+
		      ", location="+globalMenuLocation[typeI]),
		 new GlobalMenuIdeAdapter
		     (this, winMan, typeI, group, 6 , globalMenuRootCN));	    
	    
	    try{
		groupElement1.setText(((GlobalMenu) Class.forName(globalMenuRootCN + "Point1_2").newInstance()).getMenuEntry());
		groupElement2.setText(((GlobalMenu) Class.forName(globalMenuRootCN + "Point1_3").newInstance()).getMenuEntry());
		groupElement4.setText(((GlobalMenu) Class.forName(globalMenuRootCN + "Point1_4").newInstance()).getMenuEntry());
		groupElement5.setText(((GlobalMenu) Class.forName(globalMenuRootCN + "Point1_5").newInstance()).getMenuEntry());
		groupElement6.setText(((GlobalMenu) Class.forName(globalMenuRootCN + "Point1_6").newInstance()).getMenuEntry());
	    } catch (ClassNotFoundException cnfe) {
		System.err.println("keymenuextension: class cannot be located");
		System.err.println("The exception was: "+cnfe);
		cnfe.printStackTrace();
	    } catch (ExceptionInInitializerError ei) {
		System.err.println("keymenuextension: the initialization provoked "+
				   "by this method fails.");
		System.err.println("The exception was: "+ei);
		ei.printStackTrace();
	    } catch (IllegalAccessException iae) {
		System.err.println("keymenuextension: class or "+
				   "initializer is not accessible."); 
		System.err.println("The exception was: "+iae); 
		iae.printStackTrace(); 
	    } catch (InstantiationException ie) { 
		System.err.println
		    ("keymenuextension: class tried to\n"+
		     "instantiate represents an abstract class, an interface,"+
		     "an array class, a primitive type, or void; or if the"+
		     "instantiation fails for some other reason.");  
		System.err.println("The exception was: "+ie);  
		ie.printStackTrace();
	    } catch (SecurityException se) {
		System.err.println("keymenuextension: no permission to create"+
				   "a new instance"); 
		System.err.println("The exception was: "+se); 
		se.printStackTrace(); 
	    } catch (LinkageError le) {
		System.err.println("keymenuextension: linkage failed");
		System.err.println("The exception was: "+le);
		le.printStackTrace();
	    }
	    
	    groupElement1.setEnabled(true);
	    groupElement1.setVisible(true);
	    groupElement1.setSeparatorAfter(false);
	    groupElement2.setEnabled(true);
	    groupElement2.setVisible(true);
	    groupElement2.setSeparatorAfter(true);
	    groupElement4.setEnabled(true);
	    groupElement4.setVisible(true);
	    groupElement4.setSeparatorAfter(false);
	    groupElement5.setVisible(true);
	    groupElement5.setSeparatorAfter(true);
	    groupElement6.setVisible(true);
	    groupElement6.setSeparatorAfter(false);
	}
    }




    // menus for the context of a class symbol

    IdeCommandGroup myClassGroup;

    // how many classmenuitems do we have?
    static int NUMCLASSMENUITEMS = Integer.parseInt(resources.getString("key.menu.class.menuitem-count"));
    static {
	Debug.out("MenuExtension uses " + NUMCLASSMENUITEMS + " class menu items");
    }

    // IdeCommandItem is used in class ClassMenuIdeAdapter
    public IdeCommandItem[]  myClassItem = new IdeCommandItem[NUMCLASSMENUITEMS];



    private void  createClassContextMenus(){

	//creates the group-item in the context-menu
	myClassGroup = comMan.createGroup("IDOfTheClassGroup", 
					  new IdeCommandConstraints("context = element, shapeType=Class, location=popupMenu"),
					  new IdeCommandCheckListener() {
					      public void checkStatus(IdeCommandEvent event) {
						  // here we can look if we have a class or interface, ... omitted
						  myClassGroup.setText("KeY");
               
					      }
					  }
					  );   


	// All used Items in the class menu have a name 
	// starting with the following
	String classMenuRootCN = myPackageName + "." + "ClassMenu";


	for (int groupElementNo = 1; groupElementNo < (NUMCLASSMENUITEMS + 1); groupElementNo++){	
	    String optionalPlaceAfterString = "";
	    if (groupElementNo > 1){optionalPlaceAfterString = ", placeAfter = IDOfClassItem"+(groupElementNo-1);}


	    // adding the elements to the class menu

	    ClassMenuIdeAdapter actClassAdapter = new ClassMenuIdeAdapter(this, winMan, groupElementNo, classMenuRootCN);

	    myClassItem[groupElementNo-1]  = comMan.createItem
		("IDOfClassItem" + groupElementNo,
		 new IdeCommandConstraints("context = element, " +
					   "parent=IDOfTheClassGroup" +
					   optionalPlaceAfterString + 
					   ", location=popupMenu"),
		 actClassAdapter);
	}
    }


    // menus for the context of a operation

   IdeCommandGroup myOpGroup;
   IdeCommandGroup[] myOpSubGroups;
    // how many opmenuitems do we have?
    static int NUMOPMENUITEMS = Integer.parseInt(resources.getString("key.menu.op.menuitem-count"));
    static {
	Debug.out("MenuExtension uses " + NUMOPMENUITEMS + " op menu items");
    }

    // IdeCommandItem is used in class OpMenuIdeAdapter
    public IdeCommandItem[]  myOpItem = new IdeCommandItem[NUMOPMENUITEMS];



    private void createOperationContextMenus(){
	//creates the group-item in the context-menu
	myOpGroup = comMan.createGroup("IDOfTheOpGroup", 
				       new IdeCommandConstraints("context = element, shapeType=Operation, location=popupMenu"),
				       new IdeCommandCheckListener() {
					       public void checkStatus(IdeCommandEvent event) {
						   // here we can look if we have a class or interface, ... omitted
						   myOpGroup.setText("KeY");
					       }
					   }
				       );
	
	// All used Items in the class menu have a name 
	// starting with the following
	String opMenuRootCN = myPackageName + "." + "OpMenu";
	String subMenuIDs[] = new String[NUMOPMENUITEMS];
	//	String optionalPlaceAfterString = "";

	for (int groupElementNo = 1; groupElementNo < (NUMOPMENUITEMS + 1); groupElementNo++){
	    try {
		subMenuIDs[groupElementNo-1] = ((OpMenu) Class.forName(opMenuRootCN + "Point" + groupElementNo).newInstance()).getSubMenuName();
	    }catch(Exception ie) {
		Debug.fail("Class " + opMenuRootCN + "Point" + groupElementNo+ " could not be loaded");
	    }
	    if(subMenuIDs[groupElementNo-1] != null)
	    	subMenuIDs[groupElementNo-1] = "IDOf"+subMenuIDs[groupElementNo-1];

	}

	for (int groupElementNo = 1; groupElementNo < (NUMOPMENUITEMS + 1); groupElementNo++){	
	    // adding the elements to the class menu

	    //	    optionalPlaceAfterString = "";

	    // NOT NECESSARY - items are created in order 
	    //	    if ( groupElementNo > 1 ) {
	    //		optionalPlaceAfterString = ", placeAfter = IDOfOpItem" + 
	    //		    (groupElementNo-1 );
	    //	    }


	    // adding the elements to the op menu (only those not in any submenu)
	    if(subMenuIDs[groupElementNo-1] == null) {
		OpMenuIdeAdapter actOpAdapter = new OpMenuIdeAdapter ( this, 
								       winMan, 
								       groupElementNo, 
								       opMenuRootCN );

		myOpItem[groupElementNo-1]  = comMan.createItem
		    ("IDOfOpItem" + groupElementNo,
		     new IdeCommandConstraints
		     ("context = element, parent=IDOfTheOpGroup" + 
		      //		      optionalPlaceAfterString +
		      ", location=popupMenu"),
		     actOpAdapter);	    

	    }
	}

 	String[] opGroupIDs   = new String[] { "horizontal", "vertical"};
 	String[] opGroupNames = new String[] { "Horizontal Proof Obligations", 
					       "Vertical Proof Obligations"};
	myOpSubGroups = new IdeCommandGroup[opGroupIDs.length];

	for(int i=0; i<opGroupIDs.length; i++){
	    myOpSubGroups[i] = comMan.createGroup("IDOf"+opGroupIDs[i], 
					     new IdeCommandConstraints("context = element, parent=IDOfTheOpGroup, location=popupMenu"),
					     new IdeCommandCheckListener() {
						     public void checkStatus(IdeCommandEvent event) {
							 IdeCommandItem item = event.getCommandItem();
							 item.setVisible(true);
						     }
						 }
 					     );
	    myOpSubGroups[i].setText(opGroupNames[i]);
	}

	for (int groupElementNo = 1; groupElementNo < (NUMOPMENUITEMS + 1); groupElementNo++){	

	    //	    optionalPlaceAfterString = "";

	    // NOT NECESSARY - items are created in order 
	    //	    if ( groupElementNo > 1 ) {
	    //		optionalPlaceAfterString = ", placeAfter = IDOfOpItem" + 
	    //		    (groupElementNo-1 );
	    //	    }

	    // adding the elements to the op menu (only those in submenus)

	    if(subMenuIDs[groupElementNo-1] != null) {
		OpMenuIdeAdapter actOpAdapter = new OpMenuIdeAdapter ( this, 
								       winMan, 
								       groupElementNo, 
								       opMenuRootCN );

		myOpItem[groupElementNo-1]  = comMan.createItem
		    ("IDOfOpItem" + groupElementNo,
		     new IdeCommandConstraints
		     ("context = element, parent="+subMenuIDs[groupElementNo-1] + 
		      //		      optionalPlaceAfterString +
		      ", location=popupMenu"),
		     actOpAdapter);	    

	    }
	}


    }
}
