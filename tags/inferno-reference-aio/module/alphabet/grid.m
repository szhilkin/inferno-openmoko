# warning: autogenerated code; don't bother to change this, change mktypeset.b or grid.b instead
Grid: module {
	PATH: con "/dis/alphabet/grid.dis";
	Value: adt {
		b:	fn(v: self ref Value): ref Value.Vb;	# records
		e:	fn(v: self ref Value): ref Value.Ve;	# endpoint
		w:	fn(v: self ref Value): ref Value.Vw;	# wfd
		c:	fn(v: self ref Value): ref Value.Vc;	# cmd
		r:	fn(v: self ref Value): ref Value.Vr;	# status
		f:	fn(v: self ref Value): ref Value.Vf;	# fd
		s:	fn(v: self ref Value): ref Value.Vs;	# string
		typec: fn(v: self ref Value): int;
		type2s:	fn(t: int): string;
		free: fn(v: self ref Value, used: int);
		dup:	fn(v: self ref Value): ref Value;
		pick {
		Vb =>
			i: chan of ref Sys->FD;
		Ve =>
			i: chan of Endpoints->Endpoint;
		Vw =>
			i: chan of ref Sys->FD;
		Vc =>
			i: ref Sh->Cmd;
		Vr =>
			i: chan of string;
		Vf =>
			i: chan of ref Sys->FD;
		Vs =>
			i: string;
		}
	};
	init: fn();

};

Gridmodule: module {
	types: fn(): string;
	init: fn();
	run: fn(errorc: chan of string, r: ref Reports->Report,
		opts: list of (int, list of ref Grid->Value), args: list of ref Grid->Value): ref Grid->Value;
};

