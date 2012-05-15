package de.uka.ilkd.key.gui.smt;

import java.awt.Color;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;

import javax.swing.JTextPane;
import javax.swing.event.HyperlinkEvent;
import javax.swing.event.HyperlinkListener;
import javax.swing.text.BadLocationException;
import javax.swing.text.html.HTMLDocument;
import javax.swing.text.html.HTMLEditorKit;

public class ClickableMessageBox extends JTextPane{
	
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
	
	public void add(ClickableMessageBoxListener listener){
		listeners.add(listener);
	}
	
	public void add(Object item, String message, Color color){
		   try {
				kit.insertHTML(doc, doc.getLength(),
									"<a href=\""+ items.size()+
									"\" style=\"color: rgb("+color.getRed()+","+
															 color.getGreen()+","+
															 color.getBlue()+")\">"+
															 		message+"</a>", 0, 0, null);
			} catch(Throwable e){
				throw new RuntimeException(e);
			}
		   items.add(item);
		
	}
	

}
