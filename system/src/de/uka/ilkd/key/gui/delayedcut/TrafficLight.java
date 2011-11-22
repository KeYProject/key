package de.uka.ilkd.key.gui.delayedcut;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.RenderingHints;

import javax.swing.BorderFactory;
import javax.swing.JPanel;
import javax.swing.border.EtchedBorder;

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
                        // this.setBorder(BorderFactory.createLineBorder(Color.BLACK));
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
                }
               
       }