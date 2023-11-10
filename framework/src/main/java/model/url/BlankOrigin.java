package model.url;

public class BlankOrigin extends Origin {
	
	
	private static final BlankOrigin uniqueInstance = new BlankOrigin();
	
	private BlankOrigin() {
		this.originStr = "BlankOrigin";
	}
	
//	private static final String originStr = "BlankOrigin";

    public static BlankOrigin getInstance() {
        return uniqueInstance;
    }

}
