// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.utilities;

import java.awt.Color;
import java.util.ArrayList;
import java.util.LinkedList;

import javax.swing.JTextPane;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkListener;
import javax.swing.text.html.HTMLDocument;
import javax.swing.text.html.HTMLEditorKit;

/**
 * A simple textpane that supports lines that can be clicked by the users in order to trigger events.
 * It can especially be used for messages that contain detailed information that should not be showed all
 * time, but that should be accessed by clicking on a short messages summarizing the most important 
 * information.
 */
public class ClickableMessageBox extends JTextPane{
	

	private static final long serialVersionUID = 7588093268080119674L;

	public static interface ClickableMessageBoxListener{
		public void eventMessageClicked(Object object);
	}
	
	private ArrayList<Object> items = new ArrayList<Object>();
	private LinkedList<ClickableMessageBoxListener> listeners = new LinkedList<ClickableMessageBoxListener>();
	private HTMLEditorKit 	  kit = new HTMLEditorKit();
	private HTMLDocument 	  doc = new HTMLDocument();  
	
	public ClickableMessageBox(){
		this.setEditorKit(kit);
	    this.setDocument(doc);
	    this.setEditable(false);
	    this.addHyperlinkListener(new HyperlinkListener() {
			
			@Override
			public void hyperlinkUpdate(HyperlinkEvent e) {
				  if (e.getEventType() == HyperlinkEvent.EventType.ACTIVATED) 
			       {
					 int index = Integer.parseInt(e.getDescription());
					 Object item = items.get(index);
						  for(ClickableMessageBoxListener listener : listeners){
						     listener.eventMessageClicked(item);
					 }
			       }
				
			}
		});	 
	}
	
	public void clear(){
		items.clear();
		this.setText(""); 
	}
	
	public void add(ClickableMessageBoxListener listener){
		listeners.add(listener);
	}
	
	public void add(Object item, String message, Color color){
		  try {
			   if(item != null){
				kit.insertHTML(doc, doc.getLength(),
									"<u><a href=\""+ items.size()+
									"\" style=\"color: rgb("+color.getRed()+","+
															 color.getGreen()+","+
															 color.getBlue()+")\">"+
															 		message+"</a></u>", 0, 0, null);
			   }else{
					kit.insertHTML(doc, doc.getLength(),
							"<font color= rgb("+color.getRed()+","+
													 color.getGreen()+","+
													 color.getBlue()+")\">"+
													 		message+"</font>", 0, 0, null); 
			   }
			} catch(Throwable e){
				throw new RuntimeException(e);
			}
		   items.add(item);
		
	}
	

}