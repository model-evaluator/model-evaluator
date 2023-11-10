package model.url;

public class StartupOrigin extends Origin {
	
	
	private static final StartupOrigin uniqueInstance = new StartupOrigin();
	
	private StartupOrigin() {
		this.originStr = "StartupOrigin";
	}
	
//	private static final String name = "StartupOrigin";

    public static StartupOrigin getInstance() {
        return uniqueInstance;
    }

}
