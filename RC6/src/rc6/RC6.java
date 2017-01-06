
package rc6;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.Scanner;
import javax.xml.bind.DatatypeConverter;

/**
 *
 * @author Paritosh Fulara
 */
public class RC6 {
    
    	private static int w=32, r=20;
	private static int P32=0xb7e15163, Q32=0x9e3779b9;
	private static int[] SubKey;

  // This method return the Encryption block
    private static byte[] GenerateEncryptionBlocks(byte[] plaintext,byte[] key)
    {
       
      byte[] CompleteBlock=new byte[16];
      SubKey = GenerateSubkeys(key);
      
      int[] dataBlock= new int[plaintext.length/4];
     
      int registerA,registerB,registerC,registerD; 

      //fill array initially to all zero
      for(int i=0;i<dataBlock.length;i++)
       dataBlock[i]=0;
     
      int index=0;
      for(int i=0;i<dataBlock.length;i++)
      {
      dataBlock[i] =(plaintext[index++] & 0xFF)| ((plaintext[index++]& 0xFF)<<8) | ((plaintext[index++]& 0xFF)<<16)|((plaintext[index++]& 0xFF)<<24);
      }
      registerA = dataBlock[0];
      registerB = dataBlock[1];
      registerC=  dataBlock[2];
      registerD = dataBlock[3];
      
                registerB = registerB + SubKey[0];
		registerD = registerD + SubKey[1];
		for(int i = 1;i<=r;i++){
                    //log 32=5
                    
		     int resultLeftRotate_B =((registerB*(2*registerB+1))<<5) |((registerB*(2*registerB+1))>>>27);
	             int resultLeftRotate_D = ((registerD*(2*registerD+1))<<5)| ((registerD*(2*registerD+1))>>>27);
		     registerA = (((registerA^resultLeftRotate_B)<<resultLeftRotate_D)|((registerA^resultLeftRotate_B)>>>32-resultLeftRotate_D)) + SubKey[2*i];
		     registerC = (((registerC^resultLeftRotate_D)<<resultLeftRotate_B)|((registerC^resultLeftRotate_D)>>>32-resultLeftRotate_B)) + SubKey[2*i+1];
			
	                int swap = registerA;
			registerA = registerB;
			registerB = registerC;
			registerC = registerD;
			registerD = swap;
		}
		registerA = registerA + SubKey[2*r+2];
		registerC = registerC + SubKey[2*r+3];
		
		dataBlock[0] = registerA;
                dataBlock[1] = registerB;
                dataBlock[2] = registerC;
                dataBlock[3] = registerD;
		
		for(int i = 0;i<CompleteBlock.length;i++){
			CompleteBlock[i] = (byte)((dataBlock[i/4] >>> (i%4)*8) & 0xff);
		}
		
		return CompleteBlock;
    }
       
      /*
       Decryption with RC6-w/r/b
       Input: Ciphertext stored in four w-bit input registers A;B;C;D Number r of rounds w-bit round keys S[0;:::;2r + 3]
       Output: Plaintext stored in A;B;C;D
       Procedure: C = C S[2r + 3] A = A S[2r + 2] 
        for i = r downto 1 do 
        f (A;B;C;D)=(D;A;B;C)
        u =(D  (2D + 1))< < <lgw
        t =(B  (2B + 1))< < <lgw 
        C = ((C-S[2i + 1])> > >t)^u
        A = ((A-S[2i])> > >u) ^ t 
        g D = D -S[1] B = B- S[0]
       */
    
    // This method return the Decryption block
    private static byte[] GenerateDecryptionBlock(byte[] cipherText,byte[] key)
    {   
         
      byte[] CompleteBlock=new byte[16];
      
      SubKey = GenerateSubkeys(key);
      
      int[] dataBlock= new int[cipherText.length/4];
     
      int registerA,registerB,registerC,registerD; 

      //fill array initially to all zero
      for(int i=0;i<dataBlock.length;i++)
       dataBlock[i]=0;
     
      int index=0;
      for(int i=0;i<dataBlock.length;i++)
      {
      dataBlock[i] =(cipherText[index++]& 0xff)|((cipherText[index++]& 0xff)<<8)|((cipherText[index++]& 0xff)<<16)|((cipherText[index++]&0xff)<<24);
      }
      registerA = dataBlock[0];
      registerB = dataBlock[1];
      registerC=  dataBlock[2];
      registerD = dataBlock[3];
      
                registerC = registerC - SubKey[2*r+3];
		registerA = registerA - SubKey[2*r+2];
		for(int i = r;i>=1;i--){
                    //log 32=5
                    //f (A;B;C;D)=(D;A;B;C)
                    int swap = registerD;
                    registerD = registerC;
                    registerC = registerB;
                    registerB = registerA;
	            registerA = swap;
			
		    
	             int resultLeftRotate_D = ((registerD*(2*registerD+1))<<5)|((registerD*(2*registerD+1))>>>27);
                     int resultLeftRotate_B  =((registerB*(2*registerB+1))<<5)|((registerB*(2*registerB+1))>>>27);
		     registerC= (((registerC - SubKey[2*i+1])>>>resultLeftRotate_B)|((registerC - SubKey[2*i+1])<<32-resultLeftRotate_B))^ resultLeftRotate_D ;
		     registerA = (((registerA-SubKey[2*i])>>>resultLeftRotate_D)|((registerA-SubKey[2*i])<<32-resultLeftRotate_D))^ resultLeftRotate_B;
	                
		}
		registerD = registerD - SubKey[1];
		registerB = registerB - SubKey[0];
		
		dataBlock[0] = registerA;
                dataBlock[1] = registerB;
                dataBlock[2] = registerC;
                dataBlock[3] = registerD;
		
		for(int i = 0;i<CompleteBlock.length;i++){
			CompleteBlock[i] = (byte)((dataBlock[i/4] >>> (i%4)*8) & 0xff);
		}
		
		return CompleteBlock;
    }
    
    /*
   Procedure: S[0] = Pw
    for i =1to 2r +3 do 
    S[i]=S[i 1] + Qw
    A = B = i = j =0
    v =3*maxfc;2r +4
    for s =1 to v do f
    A = S[i]=(S[i]+A + B)< < <3
    B = L[j]=(L[j]+A + B)< < <(A + B)
    i =( i + 1)mod(2r + 4) 
    j =( j + 1)modc 
 */
    private static int[]  GenerateSubkeys(byte[] inputKey)
    { 
       int c=inputKey.length/4;
       int[] L = new int[c];
        for (int i = 0; i < L.length; i++)
        {
          L[i] = 0;
        }
        for (int i = 0, j = 0; i < c; i++)
        {
	  L[i] = ((inputKey[j++] & 0xFF)) | ((inputKey[j++] & 0xFF) << 8)| ((inputKey[j++] & 0xFF) << 16) | ((inputKey[j++] & 0xFF) << 24);
        }
	int[] S = new int[2*r+4];	
        S[0]=P32;
        for(int i=1;i<2*r+4;i++)
        {
            S[i] = S[i - 1] + Q32;
        }
            int A=0;
            int B=0;
            int I=0;
            int J =0;
            int v=3*Math.max(c,2*r+4);
            for(int i=0;i<v;i++)
            {
                
            A=S[I]=((S[I]+A+B)<<3)|((S[I]+A+B)>>>29);
            int x=A+B;
            B=L[J]=((L[J]+A + B)<<x)|((L[J]+A + B)>>>32-x);
            I =( I + 1)%(2*r + 4) ;
            J =( J + 1)%c;
            }
        
        return S;
    }     
    // Main function for this program ask the user to 
    public static void main(String[] args) throws FileNotFoundException, IOException {
        
        System.out.print("Press 1 for RC6 Encryption and 2 for RC6  Decryption:\n");
        Scanner reader = new Scanner(System.in); 
        int choice=reader.nextInt();
        String inputFile="";
        String outputFile="";
        int pad =0;
        String bloc="";
        byte[] plaintext;
        byte[] key;
        String KeyString="";
        String[] text=new String[10];
        FileWriter fw=null;
        BufferedWriter bw=null;
        BufferedReader br=null;
        PrintWriter pw=null;
        switch(choice)
        {
        // To handle Encryption    
        case 1:
        inputFile=args[0];
        outputFile=args[1];
        int j=0;
        
        br = new BufferedReader(new FileReader(inputFile));
			while ((text[j]=br.readLine())!= null) {
		          j++;
			}
        bloc=text[1];
        if(bloc.contains("ciphertext"))
        {
        System.out.print("Wrong file provided for Encryption! Please Check the input file and try again.");
        }
        else
        {
        bloc=bloc.replace("plaintext:", "");
        KeyString=text[2];
        KeyString=KeyString.replace("userkey:","");
        pad =0;
        bloc=bloc.replaceAll("\\s","");
        KeyString=KeyString.replaceAll("\\s","");
        pad= bloc.length()%4;
        for(int i=0;i<pad;i++)
			bloc=bloc.concat("0");
         pad = KeyString.length()%4;
        for(int i=0;i<pad;i++)
			KeyString=KeyString.concat("0");
        
        plaintext=DatatypeConverter.parseHexBinary(bloc);
        key=DatatypeConverter.parseHexBinary(KeyString);
        byte[] cipher=GenerateEncryptionBlocks(plaintext, key);
        String ciphertext=DatatypeConverter.printHexBinary(cipher);
        ciphertext=ciphertext.substring(0,32);
        //System.out.println(s);
        fw = new FileWriter(outputFile);
			pw= new PrintWriter(fw);
		pw.println("ciphertext: "+ciphertext);
                pw.close();
        }
        break;
        
        // To handle Decryption
        case 2:
        inputFile=args[0];
        outputFile=args[1];
        int k=0;
      br = new BufferedReader(new FileReader(inputFile));
			while ((text[k]=br.readLine())!= null) {
		          k++;
			}
    
        bloc=text[1];
        if(bloc.contains("plaintext"))
        {
        System.out.print("Wrong file provided for Decyption! Please Check the input file and try again");
        }
        else
        {
        bloc=bloc.replace("ciphertext:", "");
        KeyString=text[2];
        KeyString=KeyString.replace("userkey:","");
               
        pad =0;
        bloc=bloc.replaceAll("\\s","");
        KeyString=KeyString.replaceAll("\\s","");
        pad= bloc.length()%4;
        for(int i=0;i<pad;i++)
			bloc=bloc.concat("0");
         pad = KeyString.length()%4;
        for(int i=0;i<pad;i++)
			KeyString=KeyString.concat("0");
        
        plaintext=DatatypeConverter.parseHexBinary(bloc);
        key=DatatypeConverter.parseHexBinary(KeyString);
        byte[] plain=GenerateDecryptionBlock(plaintext,key);
        String plainString=DatatypeConverter.printHexBinary(plain);
        plainString=plainString.substring(0,32);
        fw = new FileWriter(outputFile);
         pw= new PrintWriter(fw);
		pw.println("plaintext: "+plainString);
       
                pw.close();
        }
        break;
       
        default:
        break;    
    }
    }
    
}
