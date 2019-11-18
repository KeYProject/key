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
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;

import javax.swing.BorderFactory;
import javax.swing.JPanel;
import javax.swing.SwingUtilities;
import javax.swing.border.EtchedBorder;


/**
 * A traffic light: It can be either green or red.
 */
class TrafficLight extends JPanel{
         private static final Color VALID_COLOR = Color.GREEN;
         private static final Color INVALID_COLOR = Color.RED;
        private static final long serialVersionUID = 1L;
        private boolean isGreen = true;
               private final int diameter;
               
               
               
               
               public TrafficLight(int diameter) {
                       super();
                        this.diameter = diameter;
                        this.setPreferredSize(new Dimension(diameter+5,2*diameter+7));
                        this.setMaximumSize(new Dimension(diameter+5,2*diameter+7));
                        this.setBorder(BorderFactory.createEtchedBorder(EtchedBorder.RAISED));
               }




               @Override
               protected void paintComponent(Graphics g) {
                       super.paintComponent(g);
                       Graphics2D g2D =(Graphics2D) g.create();
                     
                       g2D.setRenderingHint(RenderingHints.KEY_ANTIALIASING,
                                       RenderingHints.VALUE_ANTIALIAS_ON);
                       
                       g2D.setColor(Color.BLACK);
                       g2D.fillRect(0, 0, getWidth(),getHeight());
                       
                       g2D.setColor(isGreen ? VALID_COLOR : Color.LIGHT_GRAY);
                       g2D.fillOval(2, diameter+4,diameter , diameter);

                       g2D.setColor(!isGreen ? INVALID_COLOR : Color.LIGHT_GRAY);
                       g2D.fillOval(2, 2,diameter , diameter);
                
                       g2D.setColor(Color.BLACK);
                       g2D.drawOval(2, 2,diameter , diameter);
                       g2D.drawOval(2, diameter+4,diameter , diameter);
                      
                       
                       
               }
        
                 public void setGreen(boolean b){
                        isGreen = b;
                        SwingUtilities.invokeLater(new Runnable() {
                            
                            @Override
                            public void run() {
                                repaint();
                            }
                        });
                }
               
       }