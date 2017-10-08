
# spec file for package stp
#
# Copyright (c) 2017 SUSE LINUX GmbH, Nuernberg, Germany.
#
# All modifications and additions to the file contributed by third parties
# remain the property of their copyright owners, unless otherwise agreed
# upon. The license for this file, and modifications and additions to the
# file, is the same license as for the pristine package itself (unless the
# license for the pristine package is not an Open Source License, in which
# case the license is the MIT License). An "Open Source License" is a
# license that conforms to the Open Source Definition (Version 1.9)
# published by the Open Source Initiative.

# Please submit bugfixes or comments via http://bugs.opensuse.org/
#


Name:           stp
BuildRequires:  bison
%if 0%{?suse_version} > 1320
BuildRequires:  libboost_program_options-devel
%else
BuildRequires:  boost-devel
%endif
BuildRequires:  cmake
BuildRequires:  flex
BuildRequires:  gcc-c++
BuildRequires:  minisat-devel
BuildRequires:  ninja
BuildRequires:  python-devel
BuildRequires:  xz
Summary:        Constraint Solver
License:        MIT
Group:          Productivity/Scientific/Other
Version:        2.2+20170815
Release:        0
Url:            https://github.com/stp/stp/wiki
BuildRoot:      %{_tmppath}/%{name}-%{version}-build
Source0:        %{name}-%{version}.tar.xz

%description
STP is an efficient decision procedure for the validity (or satisfiability) of
formulas from a quantifier-free many-sorted theory of fixed-width bitvectors
and (non-extensional) one-dimensional arrays. The functions in STP's input
language include concatenation, extraction, left/right shift, sign-extension,
unary minus, addition, multiplication, (signed) modulo/division, bitwise
Boolean operations, if-then-else terms, and array reads and writes. The
predicates in the language include equality and (signed) comparators between
bitvector terms.

%package -n libstp2_1
Summary:        Constraint Solver
Group:          System/Libraries

%description -n libstp2_1
STP is an efficient decision procedure for the validity (or satisfiability) of
formulas from a quantifier-free many-sorted theory of fixed-width bitvectors
and (non-extensional) one-dimensional arrays. The functions in STP's input
language include concatenation, extraction, left/right shift, sign-extension,
unary minus, addition, multiplication, (signed) modulo/division, bitwise
Boolean operations, if-then-else terms, and array reads and writes. The
predicates in the language include equality and (signed) comparators between
bitvector terms.

%package devel
Summary:        Devel files for stp
Group:          Development/Languages/C and C++
Requires:       %{name} = %{version}
%if 0%{?suse_version} > 1320
Requires:       libboost_program_options-devel
%else
Requires:       boost-devel
%endif
Requires:       libstp2_1 = %{version}
Requires:       minisat-devel

%description devel
Developmnet files for stp library.

%package python
Summary:        Python bindings for stp
Group:          Development/Languages/Python
Requires:       %{name} = %{version}

%description python
Python bindings for stp library.

%prep
%setup -q

%build
%define __builder ninja
%cmake \
	-DBUILD_SHARED_LIBS:BOOL="on" \
	-DALSO_BUILD_STATIC_LIB:BOOL="off" \
	-DSTP_TIMESTAMPS:BOOL="off"
%make_jobs

%install
%cmake_install

%__install -d %{buildroot}/%{_docdir}/%{name}/example
%__install -m 644 -t %{buildroot}/%{_docdir}/%{name}/example examples/simple/*

%post -n libstp2_1 -p /sbin/ldconfig
%postun -n libstp2_1 -p /sbin/ldconfig

%files
%defattr(-,root,root)
%doc AUTHORS README.markdown LICENSE
%{_bindir}/stp*
%exclude %{_docdir}/%{name}/example/

%files -n libstp2_1
%{_libdir}/libstp.so.*

%files devel
%defattr(-,root,root)
%dir %{_includedir}/stp/
%{_includedir}/stp/*.h
%dir %{_libdir}/cmake/
%{_libdir}/libstp.so
%{_libdir}/cmake/STP/
%{_docdir}/%{name}/example/

%files python
%defattr(-,root,root)
%{python_sitelib}/*

%changelog
