/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.util.eclipse.swt.viewer;

import org.eclipse.jface.viewers.OwnerDrawLabelProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.GC;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Event;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.XMLUtil;

/**
 * <p>
 * A basic implementation of a {@link OwnerDrawLabelProvider} which renders simple HTML text.
 * </p>
 * <p>
 * Not supported tags and entities are ignored and not shown. <br>
 * Supported tags are: {@code <br>},  {@code <b>},  {@code <i>} and {@code <h2>}. <br>
 * Supported entites are: {@code &amp;},  {@code &lt;},  {@code &gt;} and numbers representing a character {@code &#...;}.
 * </p>
 * @author Martin Hentschel
 */
public abstract class AbstractSimpleHTMLLabelProvider extends OwnerDrawLabelProvider {
   /**
    * The left margin.
    */
   private final int leftMargin;

   /**
    * The right margin.
    */
   private final int rightMargin;

   /**
    * The top margin.
    */
   private final int topMargin;

   /**
    * The bottom margin.
    */
   private final int bottomMargin;
   
   /**
    * Constructor.
    */
   public AbstractSimpleHTMLLabelProvider() {
      this(2, 2, 2, 2);
   }
   
   /**
    * Constructor.
    * @param leftMargin The left margin.
    * @param rightMargin The right margin.
    * @param topMargin The top margin.
    * @param bottomMargin The bottom margin.
    */
   public AbstractSimpleHTMLLabelProvider(int leftMargin, int rightMargin, int topMargin, int bottomMargin) {
      this.leftMargin = leftMargin;
      this.rightMargin = rightMargin;
      this.topMargin = topMargin;
      this.bottomMargin = bottomMargin;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void measure(Event event, Object element) {
      String text = getHtml(element);
      Point dimension = render(event, text, false);
      event.width = leftMargin + dimension.x + rightMargin;
      event.height = topMargin + dimension.y + bottomMargin;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void paint(Event event, Object element) {
      String text = getHtml(element);
      render(event, text, true);
   }
   
   /**
    * Renders the given HTML text.
    * @param event The {@link Event} to use.
    * @param text The HTML text to render.
    * @param printToGC {@code true} to print to {@link GC} of the event, {@code false} to compute only the dimension.
    * @return The dimension of the rendered text.
    */
   protected Point render(Event event, String text, boolean printToGC) {
      if (text != null) {
         StringBuffer textSb = new StringBuffer();
         char[] signs = text.toCharArray();
         boolean inTag = false;
         boolean inAttribute = false;
         boolean lastTextIsWhitespace = false;
         StringBuffer tagSB = null;
         StringBuffer entitySB = new StringBuffer();
         boolean inEntity = false;
         int x = event.x + leftMargin;
         int y = event.y + topMargin;
         int maxHeight = 0;
         int maxWidth = 0;
         Font originalFont = event.gc.getFont();
         FontData[] datas = originalFont.getFontData();
         Font font = null;
         for (char sign : signs) {
            if (!inTag) {
               boolean entityTreated = false;
               if (inEntity) {
                  if (sign == ';') {
                     inEntity = false;
                     String entity = entitySB.toString();
                     if ("amp".equals(entity)) {
                        textSb.append('&');
                        lastTextIsWhitespace = false;
                     }
                     else if ("lt".equals(entity)) {
                        textSb.append('<');
                        lastTextIsWhitespace = false;
                     }
                     else if ("gt".equals(entity)) {
                        textSb.append('>');
                        lastTextIsWhitespace = false;
                     }
                     else if (entity.startsWith("#")) {
                        try {
                           int integer = Integer.parseInt(entity.substring(1));
                           final char character = (char)integer;
                           textSb.append(character);
                           lastTextIsWhitespace = StringUtil.WHITESPACE.contains(character + "");
                        }
                        catch (NumberFormatException e) {
                           // Nothing to do, just ignore invalid number
                        }
                     }
                     entitySB = new StringBuffer();
                     entityTreated = true;
                  }
                  else {
                     if (XMLUtil.isEntityNameCharacter(sign)) {
                        entitySB.append(sign);
                        entityTreated = true;
                     }
                     else {
                        textSb.append('&');
                        textSb.append(entitySB);
                        inEntity = false;
                        entitySB = new StringBuffer();
                     }
                  }
               }
               if (!entityTreated) {
                  if (sign == '<') {
                     inTag = true;
                     tagSB = new StringBuffer();
                     tagSB.append(sign);
                  }
                  else if (sign == '&') {
                     inEntity = true;
                  }
                  else {
                     if (StringUtil.WHITESPACE.contains(sign + "")) {
                        // whitespace
                        if (!lastTextIsWhitespace) {
                           textSb.append(' '); // Replace all whitespace by a simple space
                           lastTextIsWhitespace = true;
                        }
                     }
                     else {
                        // Not whitespace
                        textSb.append(sign);
                        lastTextIsWhitespace = false;
                     }
                  }
               }
            }
            else {
               tagSB.append(sign);
               if (sign == '>' && !inAttribute) {
                  inTag = false;
                  inAttribute = false;
                  String tag = tagSB.toString();
                  if ("<br>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     maxWidth = Math.max(maxWidth, x + point.x);
                     maxHeight = Math.max(maxHeight, point.y);
                     y += maxHeight;
                     x = event.x + leftMargin;
                     maxHeight = 0;
                     textSb = new StringBuffer();
                  }
                  else if ("<b>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, Boolean.TRUE, null, null);
                  }
                  else if ("</b>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, Boolean.FALSE, null, null);
                  }
                  else if ("<i>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, null, Boolean.TRUE, null);
                  }
                  else if ("</i>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, null, Boolean.FALSE, null);
                  }
                  else if ("<h2>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, null, null, Integer.valueOf(3));
                  }
                  else if ("</h2>".equals(tag)) {
                     Point point = printText(textSb, event, x, y, printToGC);
                     x += point.x;
                     maxWidth = Math.max(maxWidth, x);
                     maxHeight = Math.max(maxHeight, point.y);
                     textSb = new StringBuffer();
                     font = newFont(event, font, datas, null, null, Integer.valueOf(-3));
                  }
               }
               else if (sign == '\'' || sign == '"') {
                  inAttribute = !inAttribute;
               }
            }
         }
         Point point = printText(textSb, event, x, y, printToGC);
         x += point.x;
         maxHeight = Math.max(maxHeight, point.y);
         event.gc.setFont(originalFont);
         if (font != null) {
            font.dispose();
         }
         return new Point(maxWidth - leftMargin, y + maxHeight - event.y - topMargin);
      }
      else {
         return new Point(0, 0);
      }
   }
   
   /**
    * Creates a new font and sets in on the {@link GC} of the given event.
    * @param event The event.
    * @param oldFont The old {@link Font} to dispose.
    * @param datas The {@link FontData}s to modify.
    * @param changeBold If not {@code null} bold flag will be updated.
    * @param changeItalic If not {@code null} italic flag will be updated.
    * @param changeSize If not {@code null} the change to the font size.
    * @return The new {@link Font}.
    */
   protected Font newFont(Event event, Font oldFont, FontData[] datas, Boolean changeBold, Boolean changeItalic, Integer changeSize) {
      if (changeBold != null) {
         if (changeBold.booleanValue()) {
            for (FontData data : datas) {
               data.setStyle(data.getStyle() | SWT.BOLD);
            }
         }
         else {
            for (FontData data : datas) {
               data.setStyle(data.getStyle() & ~SWT.BOLD);
            }
         }
      }
      if (changeItalic != null) {
         if (changeItalic.booleanValue()) {
            for (FontData data : datas) {
               data.setStyle(data.getStyle() | SWT.ITALIC);
            }
         }
         else {
            for (FontData data : datas) {
               data.setStyle(data.getStyle() & ~SWT.ITALIC);
            }
         }
      }
      if (changeSize != null) {
         for (FontData data : datas) {
            data.setHeight(data.getHeight() + changeSize.intValue());
         }
      }
      Font newFont = new Font(event.display, datas);
      event.gc.setFont(newFont);
      if (oldFont != null) {
         oldFont.dispose();
      }
      return newFont;
   }
   
   /**
    * Prints the text to the {@link GC} of the event.
    * @param sb The {@link StringBuffer} with the text to print.
    * @param event The event.
    * @param x The x coordinate.
    * @param y The y coordinate. 
    * @param printToGC {@code true} to print to {@link GC} of the event, {@code false} to compute only the dimension.
    * @return The dimension of the printed text.
    */
   protected Point printText(StringBuffer sb, Event event, int x, int y, boolean printToGC) {
      String localText = sb.toString();
      if (printToGC) {
         event.gc.drawText(localText, x, y, true);
      }
      return event.gc.textExtent(localText);
   }
   
   /**
    * Returns the HTML text of the given element to render.
    * @param element The element.
    * @return The HTML text or {@code null} if nothing should be shown.
    */
   protected abstract String getHtml(Object element);
}