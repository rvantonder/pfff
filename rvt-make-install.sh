./configure --prefix=/home/vagrant/pfff-cust 
make depend
make
make opt
make install

# copy the scheck test requirements
cp -r ~/pfff/tests/php/scheck/* ~/pfff-cust/share/pfff/tests/php/scheck

#cd ~/pfff-cust
#bin/scheck -verbose -test 

#bin/pfff &> /tmp/test
