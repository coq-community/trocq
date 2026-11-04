{
  format = "1.0.0";

  attribute = "trocq";

  no-rocq-yet = true;

  default-bundle = "rocq-9.1";

  bundles = let
    common-bundles = {
      coq-elpi.job = true;
      trocq-std.main-job = true;
      trocq-hott.main-job = true;
    };
  in {
    "rocq-9.0" = {
      rocqPackages = { rocq-core.override.version = "9.0"; 
        rocq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
	};
      coqPackages = common-bundles // { 
        coq.override.version = "9.0"; 
        coq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
      };
    };
    "rocq-9.1" = {
      rocqPackages = { rocq-core.override.version = "9.1"; 
        rocq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
	};
      coqPackages = common-bundles // {
        coq.override.version = "9.1";
        coq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
	
      };
    };
    "rocq-9.2" = {
      rocqPackages = { rocq-core.override.version = "9.2"; 
        rocq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
	};
      coqPackages = common-bundles // {
        coq.override.version = "9.2";
        coq-elpi.override.version = "ba3cc750eda486c85d94e3eb35fb0eba77609338"; # 3.4.0. is enough for trocq-std, trocq-hott needs https://github.com/LPCIC/coq-elpi/pull/1030
	
      };
    };
    ## Trocq is broken on Rocq-master
    # "rocq-master" = {
    #   rocqPackages = {
    #     rocq-core.override.version = "master";
    #   };
    #   coqPackages = common-bundles // {
    #     coq-elpi.override.elpi-version = "3.4.2";
    #     coq-elpi.override.version = "master";
    #     coq.override.version = "master";
    #     trocq-hott.job = false; # HoTT isn't available yet for 9.1
    #     trocq-hott-examples.job = false; # HoTT isn't available yet for 9.1
    #     trocq.job = false; # depends on trocq-hott
    #   };
    # };
  };

  cachix.coq = { };
  cachix.math-comp = { };
  cachix.coq-community.authToken = "CACHIX_AUTH_TOKEN";
}
