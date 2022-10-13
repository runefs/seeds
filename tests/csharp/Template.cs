namespace csharp;
public class Template
{
   public int NoArgsWithStraightReturn() {
        return 1;
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
}
