namespace csharp;
public class Template
{

     private readonly System.Collections.Generic.IEnumerable<int> emptyInts = new int []{};
     private readonly System.Collections.Generic.IEnumerable<int> ints = new []{0,1,2,3,4,5,6,7,8,9,10};
     private readonly int[] intArray = new []{0,1,2,3,4,5,6,7,8,9,10};
     private readonly int Val = 1;
   public int NoArgsWithStraightReturn() {
        return this.Val;
   }
   public int NoArgsWithReturn() {
        return 1 +1;
   } 

   private int SimpleAdd() {
      return 1 + 1;
   }

   private int Add(int a,int b){
        return a + b;
   }   
   public int NoArgsCallingOther() {
        return SimpleAdd();
   } 

   public int NoArgsCallingOtherWithArgs() {
        return Add(1,1);
   } 

   public int CallingOtherWithArgs(int a,int b) {
        return Add(a + 1,b + 1);
   } 

   public string SimpleIf(int a) {
        if(a == 1){
          return "true";
        }
        return "false";
   }

    public string SimpleIfElse(int a) {
        var res = "";
        if(a == 1){
          res = "true";
        } else {
          res = "false";
        }
        return res;
   }

   
    public string IfElseIf(int a) {
        var res = "";
        if(a == 1){
          res = "one";
        } else if (a == 0 )  {
          res = "zero";
        } else {
          res = "big";
        }
        return res;
   }

    public string IfElseIf1() {
        return IfElseIf(1);
   }
    
   public string IfElseIf2() {
        return IfElseIf(2);
   }
   
    public string ReverseSimpleIfElse() {
        return SimpleIfElse(1);
   }

   public string ReverseSimpleIf() {
         return SimpleIf(1);
   }

   public int For(){
     var j = 0;
     for(var i = 0;i<10;i++){
          j = i;
     }
     return j;
   }

   public int While(){
     var j = 0;
     var i = 0;
     while(i<10){
          i++;
          j = i;
     }
     return j;
   }

   public int ForEachEmpty(){
     var res = 0;
     foreach(var i in emptyInts) {
          res += i; 
     }
     return res;
   }

   
   public int Foreach(){
     var res = 0;
     foreach(var i in ints) {
          res += i; 
     }
     return res;
   }


}
