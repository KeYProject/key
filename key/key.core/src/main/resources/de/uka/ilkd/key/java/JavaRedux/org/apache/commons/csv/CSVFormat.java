package org.apache.commons.csv;

public final class CSVFormat extends java.lang.Object implements java.io.Serializable {

   public static final org.apache.commons.csv.CSVFormat RFC4180;

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public org.apache.commons.csv.CSVParser parse(java.io.Reader param0) throws java.io.IOException;

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public org.apache.commons.csv.CSVPrinter print(java.lang.Appendable param0) throws java.io.IOException;

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public org.apache.commons.csv.CSVFormat withDelimiter(char param0);

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public org.apache.commons.csv.CSVFormat withFirstRecordAsHeader();

   /*@ public normal_behavior
     @ assignable \nothing;
     @*/
   public org.apache.commons.csv.CSVFormat withHeader(java.lang.String[] param0);
}