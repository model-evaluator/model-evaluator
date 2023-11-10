package model.url;

public class OpaqueOrigin extends Origin {
	
	private static final OpaqueOrigin uniqueInstance = new OpaqueOrigin();
	
	private OpaqueOrigin() {
		this.originStr = "OpaqueOrigin";
	}
	

    public static OpaqueOrigin getInstance() {
        return uniqueInstance;
    }

}
