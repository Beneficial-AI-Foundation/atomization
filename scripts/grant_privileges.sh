#!/bin/bash

mysql -u root -p${DB_PASSWORD} -e "
GRANT ALL PRIVILEGES ON ${DB_DB}.* TO 'root'@'172.%' IDENTIFIED BY '${DB_PASSWORD}';
GRANT ALL PRIVILEGES ON ${DB_DB}.* TO 'root'@'192.168.%' IDENTIFIED BY '${DB_PASSWORD}';
"
